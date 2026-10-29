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
import BstLean.Part269Direction24
import BstLean.Part269Shared24
import BstLean.Part269Finite
import BstLean.Part269Rows24
import BstLean.Part269Source
/-! Actual 12963 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12963
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12963 ≤ (1.035440922985 : ℝ) := by
  have hr : (113.855171160558 : ℝ) ≤ √(12963 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.855171160558 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12963 12963 (11 / 1000) ≤
    (0.008395639344 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12963) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.855171160558 : ℝ) ≤ √(12963 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12963)
  have hdiv : K / √(12963 : ℝ) ≤ K / 113.855171160558 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.855171160558 ≤ (0.008395639344 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12963.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12963 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12963 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12963 := gPlus_lower 12963
end BstLean.Part269.N12963

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12963
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035440922984 : ℝ) ≤ wn 12963 := by
  have hn : √(12963 : ℝ) ≤ 113.855171160559 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12963 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.855171160559 ≤ 2 / √(12963 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246682837 : ℝ) ≤ rhoBar 12963 BstLean.Part154.csC ∧
    rhoBar 12963 BstLean.Part154.csC ≤ 0.000246683219 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035440922984 : ℝ) / (1.295212 * 12963) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035440922985 : ℝ) / (1.29521 * 12963) := by gcongr
      _ ≤ (0.000246683219 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12963 BstLean.Part154.csC) ≤ 0.000986793729 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12963 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12963 BstLean.Part154.csC) (piBar (rhoBar 12963 BstLean.Part154.csC)) ≤ 0.000188418126 ∧
    cc1 (rhoBar 12963 BstLean.Part154.csC) (piBar (rhoBar 12963 BstLean.Part154.csC)) ≤ 0.000119891742 ∧
    cc2 (rhoBar 12963 BstLean.Part154.csC) ≤ 0.000069598120 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12963 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12963 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12963 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12963 BstLean.Part154.csC * nuR (rhoBar 12963 BstLean.Part154.csC)) ≤ 0.000493381652 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246683219 : ℝ) * 0.000986793729 := by gcongr
      _ ≤ (0.000493381652 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12963 BstLean.Part154.csC) * nuR (rhoBar 12963 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000986793729 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12963 BstLean.Part154.csC) * rhoBar 12963 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246683219 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246683219 / 2 + 0.399 * 0.000986793729 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188418126 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493381652 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119891742 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246683219 / 1.414213562 := by gcongr
      _ ≤ (0.000069598120 : ℝ) := by norm_num

end BstLean.Part269.N12963

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12963
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12963 BstLean.Part154.csC) (piBar (rhoBar 12963 BstLean.Part154.csC)) ≤ 1.53314E-7 := by
  have hr0 : 0 ≤ rhoBar 12963 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12963 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12963 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12963 BstLean.Part154.csC) (piBar (rhoBar 12963 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12963 BstLean.Part154.csC) (piBar (rhoBar 12963 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12963 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188418126 : ℝ) ^ 2 + 0.000119891742 ^ 2 + 3 * 0.000069598120 ^ 2 +
        2 * 0.797885 * 0.000188418126 * 0.000119891742 + 2 * 0.000188418126 * 0.000069598120 +
        4 * 0.797885 * 0.000119891742 * 0.000069598120 := by gcongr
    _ ≤ (1.53314E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12963 BstLean.Part154.csC Θ ≤ 0.002574116491 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12963 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12963 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12963 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12963 BstLean.Part154.csC) (piBar (rhoBar 12963 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12963 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035440922985 * 1.53314E-7 / (0.000246682837 : ℝ) := by gcongr
    _ ≤ 0.002574116491 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12963 BstLean.Part154.csC Θ ≤ 0.002855098147 + 0.000650436849 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12963 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12963 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12963 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035440922985 : ℝ) * ((2 * Θ * 0.000246683219 +
        (6863 / 10000) * 0.000246683219 * 12963 * 0.000986793729) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002855098147 + 0.000650436849 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12963 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12963 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12963 0.011 Θ ∧ gammaRatio 12963 0.011 Θ ≤ 0.000084803312 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12963 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035440922985 : ℝ) * 0.525 / ((1 - 0.011) * 12963) := by gcongr
      _ ≤ (0.000084803312 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12963 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12963 0.011 Θ) :=
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
    badAllowance 12963 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12963 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12963 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12963 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12963 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12963 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12963 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12963 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12963 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12963 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12963 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035440922985 : ℝ) * 12963 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12963 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003276454624 + 0.003224553340 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12963

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12963
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12963 BstLean.Part154.csC) (piBar (rhoBar 12963 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12963 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12963 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12963 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12963 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12963 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12963 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12963 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12963 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12963 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12963 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12963 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12963 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12963 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12963 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051943426599 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12963) ≤ 0.010489093898 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12963 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035440922985)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010489093898 + 2 * 0.737676 / 12963) := by gcongr
    _ ≤ (0.051943426599 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12963 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12963

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12963
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515220627 : ℝ) ≤ plow 12963 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12963) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052475945128)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351411158) : eMP 12963 0.011 xi bn ≤ 0.001163786093 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12963 : ℝ) * (1 - 0.011))) ≤ 0.000575463529 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001351411158 / (12963 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575463529 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575463529 : ℝ) + 3.141593 * 0.052475945128 / (12963 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001163786093 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052475945128)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351411158) : PiBarMP 12963 12 0.011 xi bn ≤ 0.159590522909 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12963 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036761544555 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.227236122763 : ℝ) ≤ √((12963 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.855171160558 : ℝ) ≤ √(12963 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12963) ≤ 0.122369569347 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036761544555 + 0.052475945128 * 1.772454 / (2 * (113.227236122763 : ℝ))) * (1 + 0.001163786093) +
        8 / (12963 * 113.855171160558) + 0.122369569347 := by gcongr
    _ ≤ (0.159590522909 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052475945128)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351411158) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281019713299) :
    parallelOracle 12963 0.011 xi bn cd ≤ 0.160560633403 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12963 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12963 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515220627 : ℝ) ≤ plow 12963 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.855171160558 : ℝ) ≤ √(12963 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281019713299 : ℝ) / (2 * 0.560515220627 * 113.855171160558)) * 0.159590522909 +
        0.281019713299 ^ 2 / (2 * 0.560515220627 * 113.855171160558) := by gcongr
    _ ≤ (0.160560633403 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052475945128) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351411158)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281019713299) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12963 12963 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515220627 : ℝ) ≤ plow 12963 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.855171160558 : ℝ) ≤ √(12963 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12963 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12963 Θ 1.22 ≤ 0.011647257534 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.855171160558 := by gcongr <;> linarith
      _ ≤ (0.011647257534 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12963 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12963 12963 0.011 ≤ 0.008395639344 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12963 12963 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12963 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12963 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12963 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12963 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160560633403 + 0.011647257534 + (0.008395639344 : ℝ) *
        (1 + 2 * (0.281019713299 + 0.011647257534) / (0.560515220627 * 113.855171160558))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12963]

end BstLean.Part269.N12963

/-! The original eight local profiles supply actual 12963 moment certificates. -/
namespace BstLean.Part269.N12963
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12963 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12963 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12963 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052475945128 ∧
    0 ≤ bN 12963 BstLean.Part154.csC (groupTheta g) ∧ bN 12963 BstLean.Part154.csC (groupTheta g) ≤ 0.001351411158 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12963 12963 0.011
      (momentAllowance 12963 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12963 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12963 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12963 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12963 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12963 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229076286700 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12963 0.011
      (momentAllowance 12963 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12963 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12963
/-! The actual computed-centre upper energy formula at 12963. -/
namespace BstLean.Part269.N12963
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12963

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12963
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12963)
open BstLean.Part268 (cell12963)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084757693179
  | 2 => 0.085687729514
  | 3 => 0.086614173958
  | 4 => 0.087538037664
  | 5 => 0.088460555744
  | 6 => 0.089383222041
  | 7 => 0.090307827460
  | 8 => 0.091236501942
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12963 12963 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12963 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12963

/-! Actual upper energy certificates on all 43 source endpoints at 12963. -/
namespace BstLean.Part269.N12963
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12963)
open BstLean.Part268 (cell12963)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12963 (gMinus 12963) (1 - (cell12963 i).lower) ≤ 1 ∧
    energyUpper 12963 (gMinus 12963) (BstLean.Part211.gPlus 12963)
      (finiteEnergy 12963 12963 0.011) (1 - (cell12963 i).lower) ≤
      (cell12963 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨10,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨11,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨12,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨13,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨14,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨15,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨16,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨17,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨18,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨19,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨20,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨21,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨22,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨23,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨24,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨25,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨26,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨27,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨28,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨29,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨30,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨31,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨32,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨33,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨34,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨35,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨36,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨37,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨38,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨39,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨40,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨41,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨42,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨43,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨44,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨45,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨46,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨47,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨48,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨49,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨50,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨51,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12963) (by norm_num)
        (q := 1 - (cell12963 ⟨52,by decide⟩).lower)
        (by norm_num [cell12963]) (by norm_num [cell12963])
      exact ⟨E.1,E.2.trans (by norm_num [cell12963])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12963

/-! Source-cell containment and simple scalar guards at 12963. -/
namespace BstLean.Part269.N12963
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12963)
open BstLean.Part268 (cell12963)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12963 ⟨10,by decide⟩).lower ∧ (cell12963 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12963 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12963 ⟨11,by decide⟩).lower ∧ (cell12963 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12963 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12963 ⟨12,by decide⟩).lower ∧ (cell12963 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12963 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12963 ⟨13,by decide⟩).lower ∧ (cell12963 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12963 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12963 ⟨14,by decide⟩).lower ∧ (cell12963 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12963 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12963 ⟨15,by decide⟩).lower ∧ (cell12963 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12963 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12963 ⟨16,by decide⟩).lower ∧ (cell12963 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12963 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12963 ⟨17,by decide⟩).lower ∧ (cell12963 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12963 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12963 ⟨18,by decide⟩).lower ∧ (cell12963 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12963 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12963 ⟨19,by decide⟩).lower ∧ (cell12963 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12963 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12963 ⟨20,by decide⟩).lower ∧ (cell12963 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12963 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12963 ⟨21,by decide⟩).lower ∧ (cell12963 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12963 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12963 ⟨22,by decide⟩).lower ∧ (cell12963 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12963 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12963 ⟨23,by decide⟩).lower ∧ (cell12963 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12963 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12963 ⟨24,by decide⟩).lower ∧ (cell12963 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12963 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12963 ⟨25,by decide⟩).lower ∧ (cell12963 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12963 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12963 ⟨26,by decide⟩).lower ∧ (cell12963 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12963 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12963 ⟨27,by decide⟩).lower ∧ (cell12963 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12963 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12963 ⟨28,by decide⟩).lower ∧ (cell12963 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12963 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12963 ⟨29,by decide⟩).lower ∧ (cell12963 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12963 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12963 ⟨30,by decide⟩).lower ∧ (cell12963 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12963 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12963 ⟨31,by decide⟩).lower ∧ (cell12963 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12963 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12963 ⟨32,by decide⟩).lower ∧ (cell12963 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12963 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12963 ⟨33,by decide⟩).lower ∧ (cell12963 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12963 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12963 ⟨34,by decide⟩).lower ∧ (cell12963 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12963 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12963 ⟨35,by decide⟩).lower ∧ (cell12963 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12963 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12963 ⟨36,by decide⟩).lower ∧ (cell12963 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12963 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12963 ⟨37,by decide⟩).lower ∧ (cell12963 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12963 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12963 ⟨38,by decide⟩).lower ∧ (cell12963 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12963 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12963 ⟨39,by decide⟩).lower ∧ (cell12963 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12963 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12963 ⟨40,by decide⟩).lower ∧ (cell12963 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12963 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12963 ⟨41,by decide⟩).lower ∧ (cell12963 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12963 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12963 ⟨42,by decide⟩).lower ∧ (cell12963 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12963 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12963 ⟨43,by decide⟩).lower ∧ (cell12963 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12963 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12963 ⟨44,by decide⟩).lower ∧ (cell12963 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12963 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12963 ⟨45,by decide⟩).lower ∧ (cell12963 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12963 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12963 ⟨46,by decide⟩).lower ∧ (cell12963 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12963 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12963 ⟨47,by decide⟩).lower ∧ (cell12963 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12963 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12963 ⟨48,by decide⟩).lower ∧ (cell12963 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12963 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12963 ⟨49,by decide⟩).lower ∧ (cell12963 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12963 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12963 ⟨50,by decide⟩).lower ∧ (cell12963 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12963 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12963 ⟨51,by decide⟩).lower ∧ (cell12963 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12963 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12963 ⟨52,by decide⟩).lower ∧ (cell12963 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12963 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12963 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12963 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12963,cell12963,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12963 i).lower ∧
    (cell12963 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12963 i).upper ≤ (0.532 : ℝ) ∧
    (cell12963 i).centre ≤ (0.1 : ℝ) ∧ (cell12963 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12963 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12963 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12963

/-! The local source numeric instances at 12963 have no network premises. -/
namespace BstLean.Part269.N12963
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12963)
open BstLean.Part268 (cell12963)

noncomputable def sourceNumerics12963 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12963 (cell12963 i)
      scalarRow12963.M scalarRow12963.H scalarRow12963.xi := by
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
    energy_allowance := scalarRow12963.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12963]
    centre_nonneg := (scalarRow12963.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12963])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12963
/-! Actual 12964 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12964
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12964 ≤ (1.035439544160 : ℝ) := by
  have hr : (113.859562619922 : ℝ) ≤ √(12964 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.859562619922 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12964 12964 (11 / 1000) ≤
    (0.008395315530 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12964) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.859562619922 : ℝ) ≤ √(12964 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12964)
  have hdiv : K / √(12964 : ℝ) ≤ K / 113.859562619922 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.859562619922 ≤ (0.008395315530 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12964.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12964 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12964 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12964 := gPlus_lower 12964
end BstLean.Part269.N12964

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12964
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035439544159 : ℝ) ≤ wn 12964 := by
  have hn : √(12964 : ℝ) ≤ 113.859562619923 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12964 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.859562619923 ≤ 2 / √(12964 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246663481 : ℝ) ≤ rhoBar 12964 BstLean.Part154.csC ∧
    rhoBar 12964 BstLean.Part154.csC ≤ 0.000246663863 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035439544159 : ℝ) / (1.295212 * 12964) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035439544160 : ℝ) / (1.29521 * 12964) := by gcongr
      _ ≤ (0.000246663863 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12964 BstLean.Part154.csC) ≤ 0.000986716296 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12964 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12964 BstLean.Part154.csC) (piBar (rhoBar 12964 BstLean.Part154.csC)) ≤ 0.000188403341 ∧
    cc1 (rhoBar 12964 BstLean.Part154.csC) (piBar (rhoBar 12964 BstLean.Part154.csC)) ≤ 0.000119882334 ∧
    cc2 (rhoBar 12964 BstLean.Part154.csC) ≤ 0.000069592659 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12964 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12964 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12964 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12964 BstLean.Part154.csC * nuR (rhoBar 12964 BstLean.Part154.csC)) ≤ 0.000493342937 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246663863 : ℝ) * 0.000986716296 := by gcongr
      _ ≤ (0.000493342937 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12964 BstLean.Part154.csC) * nuR (rhoBar 12964 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000986716296 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12964 BstLean.Part154.csC) * rhoBar 12964 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246663863 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246663863 / 2 + 0.399 * 0.000986716296 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188403341 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493342937 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119882334 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246663863 / 1.414213562 := by gcongr
      _ ≤ (0.000069592659 : ℝ) := by norm_num

end BstLean.Part269.N12964

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12964
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12964 BstLean.Part154.csC) (piBar (rhoBar 12964 BstLean.Part154.csC)) ≤ 1.53290E-7 := by
  have hr0 : 0 ≤ rhoBar 12964 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12964 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12964 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12964 BstLean.Part154.csC) (piBar (rhoBar 12964 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12964 BstLean.Part154.csC) (piBar (rhoBar 12964 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12964 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188403341 : ℝ) ^ 2 + 0.000119882334 ^ 2 + 3 * 0.000069592659 ^ 2 +
        2 * 0.797885 * 0.000188403341 * 0.000119882334 + 2 * 0.000188403341 * 0.000069592659 +
        4 * 0.797885 * 0.000119882334 * 0.000069592659 := by gcongr
    _ ≤ (1.53290E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12964 BstLean.Part154.csC Θ ≤ 0.002573912070 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12964 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12964 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12964 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12964 BstLean.Part154.csC) (piBar (rhoBar 12964 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12964 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035439544160 * 1.53290E-7 / (0.000246663481 : ℝ) := by gcongr
    _ ≤ 0.002573912070 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12964 BstLean.Part154.csC Θ ≤ 0.002854866515 + 0.000650384946 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12964 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12964 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12964 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035439544160 : ℝ) * ((2 * Θ * 0.000246663863 +
        (6863 / 10000) * 0.000246663863 * 12964 * 0.000986716296) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002854866515 + 0.000650384946 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12964 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12964 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12964 0.011 Θ ∧ gammaRatio 12964 0.011 Θ ≤ 0.000084796658 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12964 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035439544160 : ℝ) * 0.525 / ((1 - 0.011) * 12964) := by gcongr
      _ ≤ (0.000084796658 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12964 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12964 0.011 Θ) :=
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
    badAllowance 12964 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12964 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12964 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12964 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12964 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12964 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12964 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12964 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12964 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12964 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12964 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035439544160 : ℝ) * 12964 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12964 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003276222992 + 0.003224297016 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12964

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12964
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12964 BstLean.Part154.csC) (piBar (rhoBar 12964 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12964 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12964 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12964 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12964 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12964 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12964 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12964 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12964 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12964 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12964 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12964 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12964 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12964 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12964 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051941401688 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12964) ≤ 0.010488689344 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12964 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035439544160)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010488689344 + 2 * 0.737676 / 12964) := by gcongr
    _ ≤ (0.051941401688 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12964 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12964

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12964
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515264031 : ℝ) ≤ plow 12964 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12964) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052475578926)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351303837) : eMP 12964 0.011 xi bn ≤ 0.001163694922 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12964 : ℝ) * (1 - 0.011))) ≤ 0.000575418484 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001351303837 / (12964 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575418484 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575418484 : ℝ) + 3.141593 * 0.052475578926 / (12964 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001163694922 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052475578926)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351303837) : PiBarMP 12964 12 0.011 xi bn ≤ 0.159584319061 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12964 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036760084834 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.231603362312 : ℝ) ≤ √((12964 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.859562619922 : ℝ) ≤ √(12964 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12964) ≤ 0.122364849664 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036760084834 + 0.052475578926 * 1.772454 / (2 * (113.231603362312 : ℝ))) * (1 + 0.001163694922) +
        8 / (12964 * 113.859562619922) + 0.122364849664 := by gcongr
    _ ≤ (0.159584319061 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052475578926)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351303837) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281016889085) :
    parallelOracle 12964 0.011 xi bn cd ≤ 0.160554362438 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12964 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12964 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515264031 : ℝ) ≤ plow 12964 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.859562619922 : ℝ) ≤ √(12964 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281016889085 : ℝ) / (2 * 0.560515264031 * 113.859562619922)) * 0.159584319061 +
        0.281016889085 ^ 2 / (2 * 0.560515264031 * 113.859562619922) := by gcongr
    _ ≤ (0.160554362438 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052475578926) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351303837)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281016889085) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12964 12964 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515264031 : ℝ) ≤ plow 12964 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.859562619922 : ℝ) ≤ √(12964 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12964 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12964 Θ 1.22 ≤ 0.011646808310 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.859562619922 := by gcongr <;> linarith
      _ ≤ (0.011646808310 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12964 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12964 12964 0.011 ≤ 0.008395315530 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12964 12964 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12964 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12964 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12964 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12964 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160554362438 + 0.011646808310 + (0.008395315530 : ℝ) *
        (1 + 2 * (0.281016889085 + 0.011646808310) / (0.560515264031 * 113.859562619922))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12964]

end BstLean.Part269.N12964

/-! The original eight local profiles supply actual 12964 moment certificates. -/
namespace BstLean.Part269.N12964
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12964 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12964 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12964 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052475578926 ∧
    0 ≤ bN 12964 BstLean.Part154.csC (groupTheta g) ∧ bN 12964 BstLean.Part154.csC (groupTheta g) ≤ 0.001351303837 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12964 12964 0.011
      (momentAllowance 12964 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12964 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12964 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12964 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12964 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12964 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229075487397 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12964 0.011
      (momentAllowance 12964 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12964 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12964
/-! The actual computed-centre upper energy formula at 12964. -/
namespace BstLean.Part269.N12964
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12964

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12964
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12964)
open BstLean.Part268 (cell12964)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084755028351
  | 2 => 0.085685021046
  | 3 => 0.086611416371
  | 4 => 0.087535224162
  | 5 => 0.088457677971
  | 6 => 0.089380269809
  | 7 => 0.090304788439
  | 8 => 0.091233361318
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12964 12964 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12964 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12964

/-! Actual upper energy certificates on all 43 source endpoints at 12964. -/
namespace BstLean.Part269.N12964
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12964)
open BstLean.Part268 (cell12964)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12964 (gMinus 12964) (1 - (cell12964 i).lower) ≤ 1 ∧
    energyUpper 12964 (gMinus 12964) (BstLean.Part211.gPlus 12964)
      (finiteEnergy 12964 12964 0.011) (1 - (cell12964 i).lower) ≤
      (cell12964 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨10,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨11,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨12,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨13,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨14,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨15,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨16,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨17,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨18,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨19,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨20,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨21,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨22,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨23,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨24,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨25,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨26,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨27,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨28,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨29,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨30,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨31,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨32,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨33,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨34,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨35,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨36,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨37,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨38,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨39,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨40,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨41,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨42,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨43,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨44,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨45,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨46,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨47,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨48,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨49,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨50,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨51,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12964) (by norm_num)
        (q := 1 - (cell12964 ⟨52,by decide⟩).lower)
        (by norm_num [cell12964]) (by norm_num [cell12964])
      exact ⟨E.1,E.2.trans (by norm_num [cell12964])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12964

/-! Source-cell containment and simple scalar guards at 12964. -/
namespace BstLean.Part269.N12964
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12964)
open BstLean.Part268 (cell12964)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12964 ⟨10,by decide⟩).lower ∧ (cell12964 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12964 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12964 ⟨11,by decide⟩).lower ∧ (cell12964 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12964 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12964 ⟨12,by decide⟩).lower ∧ (cell12964 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12964 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12964 ⟨13,by decide⟩).lower ∧ (cell12964 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12964 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12964 ⟨14,by decide⟩).lower ∧ (cell12964 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12964 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12964 ⟨15,by decide⟩).lower ∧ (cell12964 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12964 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12964 ⟨16,by decide⟩).lower ∧ (cell12964 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12964 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12964 ⟨17,by decide⟩).lower ∧ (cell12964 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12964 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12964 ⟨18,by decide⟩).lower ∧ (cell12964 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12964 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12964 ⟨19,by decide⟩).lower ∧ (cell12964 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12964 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12964 ⟨20,by decide⟩).lower ∧ (cell12964 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12964 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12964 ⟨21,by decide⟩).lower ∧ (cell12964 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12964 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12964 ⟨22,by decide⟩).lower ∧ (cell12964 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12964 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12964 ⟨23,by decide⟩).lower ∧ (cell12964 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12964 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12964 ⟨24,by decide⟩).lower ∧ (cell12964 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12964 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12964 ⟨25,by decide⟩).lower ∧ (cell12964 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12964 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12964 ⟨26,by decide⟩).lower ∧ (cell12964 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12964 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12964 ⟨27,by decide⟩).lower ∧ (cell12964 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12964 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12964 ⟨28,by decide⟩).lower ∧ (cell12964 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12964 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12964 ⟨29,by decide⟩).lower ∧ (cell12964 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12964 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12964 ⟨30,by decide⟩).lower ∧ (cell12964 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12964 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12964 ⟨31,by decide⟩).lower ∧ (cell12964 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12964 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12964 ⟨32,by decide⟩).lower ∧ (cell12964 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12964 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12964 ⟨33,by decide⟩).lower ∧ (cell12964 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12964 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12964 ⟨34,by decide⟩).lower ∧ (cell12964 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12964 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12964 ⟨35,by decide⟩).lower ∧ (cell12964 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12964 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12964 ⟨36,by decide⟩).lower ∧ (cell12964 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12964 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12964 ⟨37,by decide⟩).lower ∧ (cell12964 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12964 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12964 ⟨38,by decide⟩).lower ∧ (cell12964 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12964 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12964 ⟨39,by decide⟩).lower ∧ (cell12964 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12964 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12964 ⟨40,by decide⟩).lower ∧ (cell12964 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12964 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12964 ⟨41,by decide⟩).lower ∧ (cell12964 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12964 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12964 ⟨42,by decide⟩).lower ∧ (cell12964 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12964 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12964 ⟨43,by decide⟩).lower ∧ (cell12964 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12964 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12964 ⟨44,by decide⟩).lower ∧ (cell12964 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12964 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12964 ⟨45,by decide⟩).lower ∧ (cell12964 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12964 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12964 ⟨46,by decide⟩).lower ∧ (cell12964 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12964 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12964 ⟨47,by decide⟩).lower ∧ (cell12964 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12964 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12964 ⟨48,by decide⟩).lower ∧ (cell12964 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12964 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12964 ⟨49,by decide⟩).lower ∧ (cell12964 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12964 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12964 ⟨50,by decide⟩).lower ∧ (cell12964 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12964 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12964 ⟨51,by decide⟩).lower ∧ (cell12964 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12964 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12964 ⟨52,by decide⟩).lower ∧ (cell12964 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12964 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12964 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12964 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12964,cell12964,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12964 i).lower ∧
    (cell12964 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12964 i).upper ≤ (0.532 : ℝ) ∧
    (cell12964 i).centre ≤ (0.1 : ℝ) ∧ (cell12964 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12964 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12964 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12964

/-! The local source numeric instances at 12964 have no network premises. -/
namespace BstLean.Part269.N12964
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12964)
open BstLean.Part268 (cell12964)

noncomputable def sourceNumerics12964 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12964 (cell12964 i)
      scalarRow12964.M scalarRow12964.H scalarRow12964.xi := by
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
    energy_allowance := scalarRow12964.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12964]
    centre_nonneg := (scalarRow12964.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12964])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12964
/-! Actual 12965 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12965
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12965 ≤ (1.035438165495 : ℝ) := by
  have hr : (113.863953909918 : ℝ) ≤ √(12965 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.863953909918 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12965 12965 (11 / 1000) ≤
    (0.008394991753 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12965) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.863953909918 : ℝ) ≤ √(12965 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12965)
  have hdiv : K / √(12965 : ℝ) ≤ K / 113.863953909918 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.863953909918 ≤ (0.008394991753 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12965.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12965 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12965 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12965 := gPlus_lower 12965
end BstLean.Part269.N12965

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12965
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035438165494 : ℝ) ≤ wn 12965 := by
  have hn : √(12965 : ℝ) ≤ 113.863953909919 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12965 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.863953909919 ≤ 2 / √(12965 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246644127 : ℝ) ≤ rhoBar 12965 BstLean.Part154.csC ∧
    rhoBar 12965 BstLean.Part154.csC ≤ 0.000246644509 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035438165494 : ℝ) / (1.295212 * 12965) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035438165495 : ℝ) / (1.29521 * 12965) := by gcongr
      _ ≤ (0.000246644509 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12965 BstLean.Part154.csC) ≤ 0.000986638870 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12965 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12965 BstLean.Part154.csC) (piBar (rhoBar 12965 BstLean.Part154.csC)) ≤ 0.000188388558 ∧
    cc1 (rhoBar 12965 BstLean.Part154.csC) (piBar (rhoBar 12965 BstLean.Part154.csC)) ≤ 0.000119872928 ∧
    cc2 (rhoBar 12965 BstLean.Part154.csC) ≤ 0.000069587198 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12965 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12965 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12965 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12965 BstLean.Part154.csC * nuR (rhoBar 12965 BstLean.Part154.csC)) ≤ 0.000493304227 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246644509 : ℝ) * 0.000986638870 := by gcongr
      _ ≤ (0.000493304227 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12965 BstLean.Part154.csC) * nuR (rhoBar 12965 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000986638870 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12965 BstLean.Part154.csC) * rhoBar 12965 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246644509 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246644509 / 2 + 0.399 * 0.000986638870 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188388558 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493304227 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119872928 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246644509 / 1.414213562 := by gcongr
      _ ≤ (0.000069587198 : ℝ) := by norm_num

end BstLean.Part269.N12965

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12965
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12965 BstLean.Part154.csC) (piBar (rhoBar 12965 BstLean.Part154.csC)) ≤ 1.53266E-7 := by
  have hr0 : 0 ≤ rhoBar 12965 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12965 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12965 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12965 BstLean.Part154.csC) (piBar (rhoBar 12965 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12965 BstLean.Part154.csC) (piBar (rhoBar 12965 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12965 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188388558 : ℝ) ^ 2 + 0.000119872928 ^ 2 + 3 * 0.000069587198 ^ 2 +
        2 * 0.797885 * 0.000188388558 * 0.000119872928 + 2 * 0.000188388558 * 0.000069587198 +
        4 * 0.797885 * 0.000119872928 * 0.000069587198 := by gcongr
    _ ≤ (1.53266E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12965 BstLean.Part154.csC Θ ≤ 0.002573707598 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12965 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12965 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12965 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12965 BstLean.Part154.csC) (piBar (rhoBar 12965 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12965 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035438165495 * 1.53266E-7 / (0.000246644127 : ℝ) := by gcongr
    _ ≤ 0.002573707598 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12965 BstLean.Part154.csC Θ ≤ 0.002854634894 + 0.000650333049 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12965 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12965 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12965 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035438165495 : ℝ) * ((2 * Θ * 0.000246644509 +
        (6863 / 10000) * 0.000246644509 * 12965 * 0.000986638870) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002854634894 + 0.000650333049 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12965 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12965 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12965 0.011 Θ ∧ gammaRatio 12965 0.011 Θ ≤ 0.000084790004 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12965 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035438165495 : ℝ) * 0.525 / ((1 - 0.011) * 12965) := by gcongr
      _ ≤ (0.000084790004 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12965 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12965 0.011 Θ) :=
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
    badAllowance 12965 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12965 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12965 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12965 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12965 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12965 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12965 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12965 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12965 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12965 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12965 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035438165495 : ℝ) * 12965 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12965 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003275991371 + 0.003224040647 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12965

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12965
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12965 BstLean.Part154.csC) (piBar (rhoBar 12965 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12965 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12965 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12965 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12965 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12965 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12965 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12965 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12965 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12965 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12965 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12965 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12965 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12965 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12965 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051939377009 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12965) ≤ 0.010488284836 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12965 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035438165495)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010488284836 + 2 * 0.737676 / 12965) := by gcongr
    _ ≤ (0.051939377009 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12965 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12965

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12965
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515307427 : ℝ) ≤ plow 12965 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12965) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052475212711)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351196489) : eMP 12965 0.011 xi bn ≤ 0.001163603746 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12965 : ℝ) * (1 - 0.011))) ≤ 0.000575373437 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001351196489 / (12965 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575373437 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575373437 : ℝ) + 3.141593 * 0.052475212711 / (12965 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001163603746 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052475212711)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351196489) : PiBarMP 12965 12 0.011 xi bn ≤ 0.159578115337 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12965 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036758624689 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.235970433427 : ℝ) ≤ √((12965 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.863953909918 : ℝ) ≤ √(12965 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12965) ≤ 0.122360130528 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036758624689 + 0.052475212711 * 1.772454 / (2 * (113.235970433427 : ℝ))) * (1 + 0.001163603746) +
        8 / (12965 * 113.863953909918) + 0.122360130528 := by gcongr
    _ ≤ (0.159578115337 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052475212711)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351196489) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281014065072) :
    parallelOracle 12965 0.011 xi bn cd ≤ 0.160548091606 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12965 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12965 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515307427 : ℝ) ≤ plow 12965 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.863953909918 : ℝ) ≤ √(12965 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281014065072 : ℝ) / (2 * 0.560515307427 * 113.863953909918)) * 0.159578115337 +
        0.281014065072 ^ 2 / (2 * 0.560515307427 * 113.863953909918) := by gcongr
    _ ≤ (0.160548091606 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052475212711) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351196489)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281014065072) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12965 12965 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515307427 : ℝ) ≤ plow 12965 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.863953909918 : ℝ) ≤ √(12965 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12965 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12965 Θ 1.22 ≤ 0.011646359138 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.863953909918 := by gcongr <;> linarith
      _ ≤ (0.011646359138 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12965 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12965 12965 0.011 ≤ 0.008394991753 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12965 12965 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12965 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12965 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12965 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12965 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160548091606 + 0.011646359138 + (0.008394991753 : ℝ) *
        (1 + 2 * (0.281014065072 + 0.011646359138) / (0.560515307427 * 113.863953909918))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12965]

end BstLean.Part269.N12965

/-! The original eight local profiles supply actual 12965 moment certificates. -/
namespace BstLean.Part269.N12965
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12965 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12965 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12965 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052475212711 ∧
    0 ≤ bN 12965 BstLean.Part154.csC (groupTheta g) ∧ bN 12965 BstLean.Part154.csC (groupTheta g) ≤ 0.001351196489 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12965 12965 0.011
      (momentAllowance 12965 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12965 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12965 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12965 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12965 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12965 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229074688063 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12965 0.011
      (momentAllowance 12965 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12965 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12965
/-! The actual computed-centre upper energy formula at 12965. -/
namespace BstLean.Part269.N12965
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12965

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12965
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12965)
open BstLean.Part268 (cell12965)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084752364362
  | 2 => 0.085682313448
  | 3 => 0.086608659694
  | 4 => 0.087532411617
  | 5 => 0.088454801215
  | 6 => 0.089377318665
  | 7 => 0.090301750594
  | 8 => 0.091230221975
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12965 12965 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12965 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12965

/-! Actual upper energy certificates on all 43 source endpoints at 12965. -/
namespace BstLean.Part269.N12965
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12965)
open BstLean.Part268 (cell12965)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12965 (gMinus 12965) (1 - (cell12965 i).lower) ≤ 1 ∧
    energyUpper 12965 (gMinus 12965) (BstLean.Part211.gPlus 12965)
      (finiteEnergy 12965 12965 0.011) (1 - (cell12965 i).lower) ≤
      (cell12965 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨10,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨11,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨12,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨13,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨14,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨15,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨16,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨17,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨18,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨19,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨20,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨21,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨22,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨23,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨24,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨25,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨26,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨27,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨28,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨29,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨30,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨31,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨32,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨33,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨34,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨35,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨36,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨37,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨38,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨39,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨40,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨41,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨42,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨43,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨44,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨45,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨46,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨47,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨48,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨49,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨50,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨51,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12965) (by norm_num)
        (q := 1 - (cell12965 ⟨52,by decide⟩).lower)
        (by norm_num [cell12965]) (by norm_num [cell12965])
      exact ⟨E.1,E.2.trans (by norm_num [cell12965])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12965

/-! Source-cell containment and simple scalar guards at 12965. -/
namespace BstLean.Part269.N12965
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12965)
open BstLean.Part268 (cell12965)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12965 ⟨10,by decide⟩).lower ∧ (cell12965 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12965 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12965 ⟨11,by decide⟩).lower ∧ (cell12965 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12965 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12965 ⟨12,by decide⟩).lower ∧ (cell12965 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12965 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12965 ⟨13,by decide⟩).lower ∧ (cell12965 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12965 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12965 ⟨14,by decide⟩).lower ∧ (cell12965 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12965 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12965 ⟨15,by decide⟩).lower ∧ (cell12965 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12965 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12965 ⟨16,by decide⟩).lower ∧ (cell12965 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12965 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12965 ⟨17,by decide⟩).lower ∧ (cell12965 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12965 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12965 ⟨18,by decide⟩).lower ∧ (cell12965 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12965 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12965 ⟨19,by decide⟩).lower ∧ (cell12965 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12965 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12965 ⟨20,by decide⟩).lower ∧ (cell12965 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12965 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12965 ⟨21,by decide⟩).lower ∧ (cell12965 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12965 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12965 ⟨22,by decide⟩).lower ∧ (cell12965 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12965 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12965 ⟨23,by decide⟩).lower ∧ (cell12965 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12965 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12965 ⟨24,by decide⟩).lower ∧ (cell12965 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12965 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12965 ⟨25,by decide⟩).lower ∧ (cell12965 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12965 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12965 ⟨26,by decide⟩).lower ∧ (cell12965 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12965 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12965 ⟨27,by decide⟩).lower ∧ (cell12965 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12965 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12965 ⟨28,by decide⟩).lower ∧ (cell12965 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12965 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12965 ⟨29,by decide⟩).lower ∧ (cell12965 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12965 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12965 ⟨30,by decide⟩).lower ∧ (cell12965 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12965 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12965 ⟨31,by decide⟩).lower ∧ (cell12965 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12965 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12965 ⟨32,by decide⟩).lower ∧ (cell12965 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12965 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12965 ⟨33,by decide⟩).lower ∧ (cell12965 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12965 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12965 ⟨34,by decide⟩).lower ∧ (cell12965 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12965 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12965 ⟨35,by decide⟩).lower ∧ (cell12965 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12965 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12965 ⟨36,by decide⟩).lower ∧ (cell12965 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12965 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12965 ⟨37,by decide⟩).lower ∧ (cell12965 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12965 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12965 ⟨38,by decide⟩).lower ∧ (cell12965 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12965 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12965 ⟨39,by decide⟩).lower ∧ (cell12965 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12965 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12965 ⟨40,by decide⟩).lower ∧ (cell12965 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12965 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12965 ⟨41,by decide⟩).lower ∧ (cell12965 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12965 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12965 ⟨42,by decide⟩).lower ∧ (cell12965 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12965 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12965 ⟨43,by decide⟩).lower ∧ (cell12965 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12965 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12965 ⟨44,by decide⟩).lower ∧ (cell12965 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12965 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12965 ⟨45,by decide⟩).lower ∧ (cell12965 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12965 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12965 ⟨46,by decide⟩).lower ∧ (cell12965 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12965 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12965 ⟨47,by decide⟩).lower ∧ (cell12965 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12965 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12965 ⟨48,by decide⟩).lower ∧ (cell12965 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12965 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12965 ⟨49,by decide⟩).lower ∧ (cell12965 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12965 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12965 ⟨50,by decide⟩).lower ∧ (cell12965 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12965 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12965 ⟨51,by decide⟩).lower ∧ (cell12965 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12965 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12965 ⟨52,by decide⟩).lower ∧ (cell12965 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12965 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12965 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12965 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12965,cell12965,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12965 i).lower ∧
    (cell12965 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12965 i).upper ≤ (0.532 : ℝ) ∧
    (cell12965 i).centre ≤ (0.1 : ℝ) ∧ (cell12965 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12965 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12965 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12965

/-! The local source numeric instances at 12965 have no network premises. -/
namespace BstLean.Part269.N12965
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12965)
open BstLean.Part268 (cell12965)

noncomputable def sourceNumerics12965 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12965 (cell12965 i)
      scalarRow12965.M scalarRow12965.H scalarRow12965.xi := by
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
    energy_allowance := scalarRow12965.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12965]
    centre_nonneg := (scalarRow12965.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12965])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12965
/-! Actual 12966 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12966
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12966 ≤ (1.035436786991 : ℝ) := by
  have hr : (113.868345030565 : ℝ) ≤ √(12966 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.868345030565 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12966 12966 (11 / 1000) ≤
    (0.008394668013 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12966) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.868345030565 : ℝ) ≤ √(12966 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12966)
  have hdiv : K / √(12966 : ℝ) ≤ K / 113.868345030565 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.868345030565 ≤ (0.008394668013 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12966.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12966 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12966 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12966 := gPlus_lower 12966
end BstLean.Part269.N12966

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12966
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035436786990 : ℝ) ≤ wn 12966 := by
  have hn : √(12966 : ℝ) ≤ 113.868345030566 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12966 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.868345030566 ≤ 2 / √(12966 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246624776 : ℝ) ≤ rhoBar 12966 BstLean.Part154.csC ∧
    rhoBar 12966 BstLean.Part154.csC ≤ 0.000246625158 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035436786990 : ℝ) / (1.295212 * 12966) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035436786991 : ℝ) / (1.29521 * 12966) := by gcongr
      _ ≤ (0.000246625158 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12966 BstLean.Part154.csC) ≤ 0.000986561456 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12966 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12966 BstLean.Part154.csC) (piBar (rhoBar 12966 BstLean.Part154.csC)) ≤ 0.000188373777 ∧
    cc1 (rhoBar 12966 BstLean.Part154.csC) (piBar (rhoBar 12966 BstLean.Part154.csC)) ≤ 0.000119863522 ∧
    cc2 (rhoBar 12966 BstLean.Part154.csC) ≤ 0.000069581739 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12966 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12966 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12966 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12966 BstLean.Part154.csC * nuR (rhoBar 12966 BstLean.Part154.csC)) ≤ 0.000493265522 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246625158 : ℝ) * 0.000986561456 := by gcongr
      _ ≤ (0.000493265522 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12966 BstLean.Part154.csC) * nuR (rhoBar 12966 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000986561456 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12966 BstLean.Part154.csC) * rhoBar 12966 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246625158 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246625158 / 2 + 0.399 * 0.000986561456 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188373777 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493265522 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119863522 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246625158 / 1.414213562 := by gcongr
      _ ≤ (0.000069581739 : ℝ) := by norm_num

end BstLean.Part269.N12966

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12966
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12966 BstLean.Part154.csC) (piBar (rhoBar 12966 BstLean.Part154.csC)) ≤ 1.53242E-7 := by
  have hr0 : 0 ≤ rhoBar 12966 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12966 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12966 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12966 BstLean.Part154.csC) (piBar (rhoBar 12966 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12966 BstLean.Part154.csC) (piBar (rhoBar 12966 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12966 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188373777 : ℝ) ^ 2 + 0.000119863522 ^ 2 + 3 * 0.000069581739 ^ 2 +
        2 * 0.797885 * 0.000188373777 * 0.000119863522 + 2 * 0.000188373777 * 0.000069581739 +
        4 * 0.797885 * 0.000119863522 * 0.000069581739 := by gcongr
    _ ≤ (1.53242E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12966 BstLean.Part154.csC Θ ≤ 0.002573503064 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12966 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12966 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12966 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12966 BstLean.Part154.csC) (piBar (rhoBar 12966 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12966 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035436786991 * 1.53242E-7 / (0.000246624776 : ℝ) := by gcongr
    _ ≤ 0.002573503064 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12966 BstLean.Part154.csC Θ ≤ 0.002854403310 + 0.000650281160 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12966 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12966 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12966 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035436786991 : ℝ) * ((2 * Θ * 0.000246625158 +
        (6863 / 10000) * 0.000246625158 * 12966 * 0.000986561456) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002854403310 + 0.000650281160 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12966 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12966 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12966 0.011 Θ ∧ gammaRatio 12966 0.011 Θ ≤ 0.000084783352 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12966 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035436786991 : ℝ) * 0.525 / ((1 - 0.011) * 12966) := by gcongr
      _ ≤ (0.000084783352 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12966 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12966 0.011 Θ) :=
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
    badAllowance 12966 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12966 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12966 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12966 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12966 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12966 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12966 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12966 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12966 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12966 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12966 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035436786991 : ℝ) * 12966 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12966 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003275759787 + 0.003223784224 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12966

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12966
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12966 BstLean.Part154.csC) (piBar (rhoBar 12966 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12966 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12966 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12966 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12966 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12966 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12966 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12966 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12966 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12966 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12966 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12966 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12966 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12966 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12966 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051937352563 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12966) ≤ 0.010487880374 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12966 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035436786991)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010487880374 + 2 * 0.737676 / 12966) := by gcongr
    _ ≤ (0.051937352563 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12966 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12966

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12966
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515350817 : ℝ) ≤ plow 12966 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12966) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052474846505)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351089109) : eMP 12966 0.011 xi bn ≤ 0.001163512565 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12966 : ℝ) * (1 - 0.011))) ≤ 0.000575328387 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001351089109 / (12966 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575328387 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575328387 : ℝ) + 3.141593 * 0.052474846505 / (12966 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001163512565 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052474846505)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351089109) : PiBarMP 12966 12 0.011 xi bn ≤ 0.159571911668 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12966 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036757164051 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.240337336127 : ℝ) ≤ √((12966 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.868345030565 : ℝ) ≤ √(12966 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12966) ≤ 0.122355411937 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036757164051 + 0.052474846505 * 1.772454 / (2 * (113.240337336127 : ℝ))) * (1 + 0.001163512565) +
        8 / (12966 * 113.868345030565) + 0.122355411937 := by gcongr
    _ ≤ (0.159571911668 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052474846505)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351089109) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281011241309) :
    parallelOracle 12966 0.011 xi bn cd ≤ 0.160541820837 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12966 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12966 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515350817 : ℝ) ≤ plow 12966 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.868345030565 : ℝ) ≤ √(12966 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281011241309 : ℝ) / (2 * 0.560515350817 * 113.868345030565)) * 0.159571911668 +
        0.281011241309 ^ 2 / (2 * 0.560515350817 * 113.868345030565) := by gcongr
    _ ≤ (0.160541820837 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052474846505) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001351089109)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281011241309) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12966 12966 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515350817 : ℝ) ≤ plow 12966 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.868345030565 : ℝ) ≤ √(12966 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12966 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12966 Θ 1.22 ≤ 0.011645910017 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.868345030565 := by gcongr <;> linarith
      _ ≤ (0.011645910017 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12966 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12966 12966 0.011 ≤ 0.008394668013 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12966 12966 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12966 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12966 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12966 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12966 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160541820837 + 0.011645910017 + (0.008394668013 : ℝ) *
        (1 + 2 * (0.281011241309 + 0.011645910017) / (0.560515350817 * 113.868345030565))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12966]

end BstLean.Part269.N12966

/-! The original eight local profiles supply actual 12966 moment certificates. -/
namespace BstLean.Part269.N12966
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12966 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12966 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12966 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052474846505 ∧
    0 ≤ bN 12966 BstLean.Part154.csC (groupTheta g) ∧ bN 12966 BstLean.Part154.csC (groupTheta g) ≤ 0.001351089109 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12966 12966 0.011
      (momentAllowance 12966 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12966 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12966 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12966 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12966 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12966 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229073888746 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12966 0.011
      (momentAllowance 12966 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12966 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12966
/-! The actual computed-centre upper energy formula at 12966. -/
namespace BstLean.Part269.N12966
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12966

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12966
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12966)
open BstLean.Part268 (cell12966)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084749701209
  | 2 => 0.085679606719
  | 3 => 0.086605903924
  | 4 => 0.087529600028
  | 5 => 0.088451925473
  | 6 => 0.089374368608
  | 7 => 0.090298713923
  | 8 => 0.091227083911
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12966 12966 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12966 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12966

/-! Actual upper energy certificates on all 43 source endpoints at 12966. -/
namespace BstLean.Part269.N12966
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12966)
open BstLean.Part268 (cell12966)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12966 (gMinus 12966) (1 - (cell12966 i).lower) ≤ 1 ∧
    energyUpper 12966 (gMinus 12966) (BstLean.Part211.gPlus 12966)
      (finiteEnergy 12966 12966 0.011) (1 - (cell12966 i).lower) ≤
      (cell12966 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨10,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨11,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨12,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨13,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨14,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨15,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨16,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨17,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨18,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨19,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨20,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨21,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨22,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨23,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨24,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨25,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨26,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨27,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨28,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨29,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨30,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨31,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨32,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨33,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨34,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨35,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨36,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨37,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨38,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨39,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨40,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨41,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨42,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨43,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨44,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨45,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨46,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨47,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨48,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨49,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨50,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨51,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12966) (by norm_num)
        (q := 1 - (cell12966 ⟨52,by decide⟩).lower)
        (by norm_num [cell12966]) (by norm_num [cell12966])
      exact ⟨E.1,E.2.trans (by norm_num [cell12966])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12966

/-! Source-cell containment and simple scalar guards at 12966. -/
namespace BstLean.Part269.N12966
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12966)
open BstLean.Part268 (cell12966)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12966 ⟨10,by decide⟩).lower ∧ (cell12966 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12966 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12966 ⟨11,by decide⟩).lower ∧ (cell12966 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12966 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12966 ⟨12,by decide⟩).lower ∧ (cell12966 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12966 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12966 ⟨13,by decide⟩).lower ∧ (cell12966 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12966 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12966 ⟨14,by decide⟩).lower ∧ (cell12966 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12966 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12966 ⟨15,by decide⟩).lower ∧ (cell12966 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12966 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12966 ⟨16,by decide⟩).lower ∧ (cell12966 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12966 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12966 ⟨17,by decide⟩).lower ∧ (cell12966 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12966 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12966 ⟨18,by decide⟩).lower ∧ (cell12966 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12966 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12966 ⟨19,by decide⟩).lower ∧ (cell12966 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12966 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12966 ⟨20,by decide⟩).lower ∧ (cell12966 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12966 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12966 ⟨21,by decide⟩).lower ∧ (cell12966 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12966 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12966 ⟨22,by decide⟩).lower ∧ (cell12966 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12966 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12966 ⟨23,by decide⟩).lower ∧ (cell12966 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12966 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12966 ⟨24,by decide⟩).lower ∧ (cell12966 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12966 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12966 ⟨25,by decide⟩).lower ∧ (cell12966 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12966 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12966 ⟨26,by decide⟩).lower ∧ (cell12966 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12966 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12966 ⟨27,by decide⟩).lower ∧ (cell12966 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12966 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12966 ⟨28,by decide⟩).lower ∧ (cell12966 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12966 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12966 ⟨29,by decide⟩).lower ∧ (cell12966 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12966 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12966 ⟨30,by decide⟩).lower ∧ (cell12966 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12966 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12966 ⟨31,by decide⟩).lower ∧ (cell12966 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12966 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12966 ⟨32,by decide⟩).lower ∧ (cell12966 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12966 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12966 ⟨33,by decide⟩).lower ∧ (cell12966 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12966 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12966 ⟨34,by decide⟩).lower ∧ (cell12966 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12966 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12966 ⟨35,by decide⟩).lower ∧ (cell12966 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12966 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12966 ⟨36,by decide⟩).lower ∧ (cell12966 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12966 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12966 ⟨37,by decide⟩).lower ∧ (cell12966 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12966 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12966 ⟨38,by decide⟩).lower ∧ (cell12966 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12966 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12966 ⟨39,by decide⟩).lower ∧ (cell12966 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12966 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12966 ⟨40,by decide⟩).lower ∧ (cell12966 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12966 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12966 ⟨41,by decide⟩).lower ∧ (cell12966 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12966 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12966 ⟨42,by decide⟩).lower ∧ (cell12966 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12966 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12966 ⟨43,by decide⟩).lower ∧ (cell12966 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12966 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12966 ⟨44,by decide⟩).lower ∧ (cell12966 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12966 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12966 ⟨45,by decide⟩).lower ∧ (cell12966 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12966 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12966 ⟨46,by decide⟩).lower ∧ (cell12966 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12966 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12966 ⟨47,by decide⟩).lower ∧ (cell12966 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12966 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12966 ⟨48,by decide⟩).lower ∧ (cell12966 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12966 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12966 ⟨49,by decide⟩).lower ∧ (cell12966 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12966 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12966 ⟨50,by decide⟩).lower ∧ (cell12966 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12966 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12966 ⟨51,by decide⟩).lower ∧ (cell12966 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12966 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12966 ⟨52,by decide⟩).lower ∧ (cell12966 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12966 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12966 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12966 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12966,cell12966,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12966 i).lower ∧
    (cell12966 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12966 i).upper ≤ (0.532 : ℝ) ∧
    (cell12966 i).centre ≤ (0.1 : ℝ) ∧ (cell12966 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12966 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12966 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12966

/-! The local source numeric instances at 12966 have no network premises. -/
namespace BstLean.Part269.N12966
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12966)
open BstLean.Part268 (cell12966)

noncomputable def sourceNumerics12966 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12966 (cell12966 i)
      scalarRow12966.M scalarRow12966.H scalarRow12966.xi := by
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
    energy_allowance := scalarRow12966.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12966]
    centre_nonneg := (scalarRow12966.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12966])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12966
/-! Actual 12967 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12967
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12967 ≤ (1.035435408648 : ℝ) := by
  have hr : (113.872735981884 : ℝ) ≤ √(12967 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.872735981884 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12967 12967 (11 / 1000) ≤
    (0.008394344311 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12967) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.872735981884 : ℝ) ≤ √(12967 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12967)
  have hdiv : K / √(12967 : ℝ) ≤ K / 113.872735981884 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.872735981884 ≤ (0.008394344311 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12967.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12967 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12967 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12967 := gPlus_lower 12967
end BstLean.Part269.N12967

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12967
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035435408647 : ℝ) ≤ wn 12967 := by
  have hn : √(12967 : ℝ) ≤ 113.872735981885 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12967 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.872735981885 ≤ 2 / √(12967 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246605429 : ℝ) ≤ rhoBar 12967 BstLean.Part154.csC ∧
    rhoBar 12967 BstLean.Part154.csC ≤ 0.000246605810 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035435408647 : ℝ) / (1.295212 * 12967) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035435408648 : ℝ) / (1.29521 * 12967) := by gcongr
      _ ≤ (0.000246605810 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12967 BstLean.Part154.csC) ≤ 0.000986484055 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12967 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12967 BstLean.Part154.csC) (piBar (rhoBar 12967 BstLean.Part154.csC)) ≤ 0.000188358998 ∧
    cc1 (rhoBar 12967 BstLean.Part154.csC) (piBar (rhoBar 12967 BstLean.Part154.csC)) ≤ 0.000119854119 ∧
    cc2 (rhoBar 12967 BstLean.Part154.csC) ≤ 0.000069576280 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12967 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12967 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12967 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12967 BstLean.Part154.csC * nuR (rhoBar 12967 BstLean.Part154.csC)) ≤ 0.000493226824 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246605810 : ℝ) * 0.000986484055 := by gcongr
      _ ≤ (0.000493226824 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12967 BstLean.Part154.csC) * nuR (rhoBar 12967 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000986484055 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12967 BstLean.Part154.csC) * rhoBar 12967 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246605810 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246605810 / 2 + 0.399 * 0.000986484055 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188358998 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493226824 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119854119 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246605810 / 1.414213562 := by gcongr
      _ ≤ (0.000069576280 : ℝ) := by norm_num

end BstLean.Part269.N12967

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12967
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12967 BstLean.Part154.csC) (piBar (rhoBar 12967 BstLean.Part154.csC)) ≤ 1.53218E-7 := by
  have hr0 : 0 ≤ rhoBar 12967 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12967 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12967 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12967 BstLean.Part154.csC) (piBar (rhoBar 12967 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12967 BstLean.Part154.csC) (piBar (rhoBar 12967 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12967 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188358998 : ℝ) ^ 2 + 0.000119854119 ^ 2 + 3 * 0.000069576280 ^ 2 +
        2 * 0.797885 * 0.000188358998 * 0.000119854119 + 2 * 0.000188358998 * 0.000069576280 +
        4 * 0.797885 * 0.000119854119 * 0.000069576280 := by gcongr
    _ ≤ (1.53218E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12967 BstLean.Part154.csC Θ ≤ 0.002573298457 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12967 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12967 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12967 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12967 BstLean.Part154.csC) (piBar (rhoBar 12967 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12967 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035435408648 * 1.53218E-7 / (0.000246605429 : ℝ) := by gcongr
    _ ≤ 0.002573298457 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12967 BstLean.Part154.csC Θ ≤ 0.002854171764 + 0.000650229280 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12967 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12967 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12967 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035435408648 : ℝ) * ((2 * Θ * 0.000246605810 +
        (6863 / 10000) * 0.000246605810 * 12967 * 0.000986484055) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002854171764 + 0.000650229280 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12967 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12967 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12967 0.011 Θ ∧ gammaRatio 12967 0.011 Θ ≤ 0.000084776701 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12967 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035435408648 : ℝ) * 0.525 / ((1 - 0.011) * 12967) := by gcongr
      _ ≤ (0.000084776701 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12967 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12967 0.011 Θ) :=
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
    badAllowance 12967 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12967 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12967 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12967 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12967 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12967 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12967 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12967 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12967 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12967 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12967 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035435408648 : ℝ) * 12967 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12967 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003275528241 + 0.003223527737 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12967

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12967
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12967 BstLean.Part154.csC) (piBar (rhoBar 12967 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12967 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12967 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12967 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12967 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12967 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12967 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12967 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12967 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12967 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12967 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12967 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12967 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12967 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12967 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051935328358 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12967) ≤ 0.010487475960 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12967 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035435408648)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010487475960 + 2 * 0.737676 / 12967) := by gcongr
    _ ≤ (0.051935328358 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12967 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12967

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12967
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515394200 : ℝ) ≤ plow 12967 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12967) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052474480303)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350981690) : eMP 12967 0.011 xi bn ≤ 0.001163421374 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12967 : ℝ) * (1 - 0.011))) ≤ 0.000575283332 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001350981690 / (12967 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575283332 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575283332 : ℝ) + 3.141593 * 0.052474480303 / (12967 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001163421374 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052474480303)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350981690) : PiBarMP 12967 12 0.011 xi bn ≤ 0.159565707955 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12967 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036755702823 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.244704070433 : ℝ) ≤ √((12967 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.872735981884 : ℝ) ≤ √(12967 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12967) ≤ 0.122350693892 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036755702823 + 0.052474480303 * 1.772454 / (2 * (113.244704070433 : ℝ))) * (1 + 0.001163421374) +
        8 / (12967 * 113.872735981884) + 0.122350693892 := by gcongr
    _ ≤ (0.159565707955 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052474480303)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350981690) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281008417793) :
    parallelOracle 12967 0.011 xi bn cd ≤ 0.160535550032 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12967 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12967 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515394200 : ℝ) ≤ plow 12967 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.872735981884 : ℝ) ≤ √(12967 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281008417793 : ℝ) / (2 * 0.560515394200 * 113.872735981884)) * 0.159565707955 +
        0.281008417793 ^ 2 / (2 * 0.560515394200 * 113.872735981884) := by gcongr
    _ ≤ (0.160535550032 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052474480303) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350981690)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281008417793) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12967 12967 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515394200 : ℝ) ≤ plow 12967 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.872735981884 : ℝ) ≤ √(12967 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12967 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12967 Θ 1.22 ≤ 0.011645460949 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.872735981884 := by gcongr <;> linarith
      _ ≤ (0.011645460949 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12967 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12967 12967 0.011 ≤ 0.008394344311 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12967 12967 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12967 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12967 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12967 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12967 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160535550032 + 0.011645460949 + (0.008394344311 : ℝ) *
        (1 + 2 * (0.281008417793 + 0.011645460949) / (0.560515394200 * 113.872735981884))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12967]

end BstLean.Part269.N12967

/-! The original eight local profiles supply actual 12967 moment certificates. -/
namespace BstLean.Part269.N12967
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12967 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12967 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12967 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052474480303 ∧
    0 ≤ bN 12967 BstLean.Part154.csC (groupTheta g) ∧ bN 12967 BstLean.Part154.csC (groupTheta g) ≤ 0.001350981690 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12967 12967 0.011
      (momentAllowance 12967 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12967 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12967 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12967 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12967 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12967 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229073089435 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12967 0.011
      (momentAllowance 12967 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12967 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12967
/-! The actual computed-centre upper energy formula at 12967. -/
namespace BstLean.Part269.N12967
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12967

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12967
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12967)
open BstLean.Part268 (cell12967)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084747038894
  | 2 => 0.085676900858
  | 3 => 0.086603149061
  | 4 => 0.087526789394
  | 5 => 0.088449050745
  | 6 => 0.089371419637
  | 7 => 0.090295678424
  | 8 => 0.091223947125
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12967 12967 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12967 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12967

/-! Actual upper energy certificates on all 43 source endpoints at 12967. -/
namespace BstLean.Part269.N12967
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12967)
open BstLean.Part268 (cell12967)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12967 (gMinus 12967) (1 - (cell12967 i).lower) ≤ 1 ∧
    energyUpper 12967 (gMinus 12967) (BstLean.Part211.gPlus 12967)
      (finiteEnergy 12967 12967 0.011) (1 - (cell12967 i).lower) ≤
      (cell12967 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨10,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨11,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨12,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨13,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨14,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨15,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨16,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨17,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨18,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨19,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨20,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨21,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨22,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨23,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨24,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨25,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨26,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨27,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨28,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨29,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨30,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨31,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨32,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨33,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨34,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨35,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨36,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨37,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨38,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨39,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨40,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨41,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨42,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨43,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨44,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨45,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨46,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨47,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨48,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨49,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨50,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨51,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12967) (by norm_num)
        (q := 1 - (cell12967 ⟨52,by decide⟩).lower)
        (by norm_num [cell12967]) (by norm_num [cell12967])
      exact ⟨E.1,E.2.trans (by norm_num [cell12967])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12967

/-! Source-cell containment and simple scalar guards at 12967. -/
namespace BstLean.Part269.N12967
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12967)
open BstLean.Part268 (cell12967)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12967 ⟨10,by decide⟩).lower ∧ (cell12967 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12967 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12967 ⟨11,by decide⟩).lower ∧ (cell12967 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12967 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12967 ⟨12,by decide⟩).lower ∧ (cell12967 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12967 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12967 ⟨13,by decide⟩).lower ∧ (cell12967 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12967 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12967 ⟨14,by decide⟩).lower ∧ (cell12967 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12967 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12967 ⟨15,by decide⟩).lower ∧ (cell12967 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12967 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12967 ⟨16,by decide⟩).lower ∧ (cell12967 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12967 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12967 ⟨17,by decide⟩).lower ∧ (cell12967 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12967 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12967 ⟨18,by decide⟩).lower ∧ (cell12967 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12967 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12967 ⟨19,by decide⟩).lower ∧ (cell12967 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12967 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12967 ⟨20,by decide⟩).lower ∧ (cell12967 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12967 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12967 ⟨21,by decide⟩).lower ∧ (cell12967 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12967 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12967 ⟨22,by decide⟩).lower ∧ (cell12967 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12967 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12967 ⟨23,by decide⟩).lower ∧ (cell12967 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12967 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12967 ⟨24,by decide⟩).lower ∧ (cell12967 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12967 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12967 ⟨25,by decide⟩).lower ∧ (cell12967 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12967 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12967 ⟨26,by decide⟩).lower ∧ (cell12967 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12967 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12967 ⟨27,by decide⟩).lower ∧ (cell12967 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12967 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12967 ⟨28,by decide⟩).lower ∧ (cell12967 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12967 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12967 ⟨29,by decide⟩).lower ∧ (cell12967 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12967 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12967 ⟨30,by decide⟩).lower ∧ (cell12967 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12967 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12967 ⟨31,by decide⟩).lower ∧ (cell12967 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12967 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12967 ⟨32,by decide⟩).lower ∧ (cell12967 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12967 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12967 ⟨33,by decide⟩).lower ∧ (cell12967 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12967 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12967 ⟨34,by decide⟩).lower ∧ (cell12967 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12967 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12967 ⟨35,by decide⟩).lower ∧ (cell12967 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12967 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12967 ⟨36,by decide⟩).lower ∧ (cell12967 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12967 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12967 ⟨37,by decide⟩).lower ∧ (cell12967 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12967 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12967 ⟨38,by decide⟩).lower ∧ (cell12967 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12967 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12967 ⟨39,by decide⟩).lower ∧ (cell12967 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12967 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12967 ⟨40,by decide⟩).lower ∧ (cell12967 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12967 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12967 ⟨41,by decide⟩).lower ∧ (cell12967 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12967 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12967 ⟨42,by decide⟩).lower ∧ (cell12967 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12967 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12967 ⟨43,by decide⟩).lower ∧ (cell12967 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12967 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12967 ⟨44,by decide⟩).lower ∧ (cell12967 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12967 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12967 ⟨45,by decide⟩).lower ∧ (cell12967 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12967 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12967 ⟨46,by decide⟩).lower ∧ (cell12967 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12967 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12967 ⟨47,by decide⟩).lower ∧ (cell12967 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12967 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12967 ⟨48,by decide⟩).lower ∧ (cell12967 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12967 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12967 ⟨49,by decide⟩).lower ∧ (cell12967 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12967 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12967 ⟨50,by decide⟩).lower ∧ (cell12967 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12967 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12967 ⟨51,by decide⟩).lower ∧ (cell12967 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12967 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12967 ⟨52,by decide⟩).lower ∧ (cell12967 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12967 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12967 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12967 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12967,cell12967,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12967 i).lower ∧
    (cell12967 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12967 i).upper ≤ (0.532 : ℝ) ∧
    (cell12967 i).centre ≤ (0.1 : ℝ) ∧ (cell12967 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12967 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12967 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12967

/-! The local source numeric instances at 12967 have no network premises. -/
namespace BstLean.Part269.N12967
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12967)
open BstLean.Part268 (cell12967)

noncomputable def sourceNumerics12967 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12967 (cell12967 i)
      scalarRow12967.M scalarRow12967.H scalarRow12967.xi := by
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
    energy_allowance := scalarRow12967.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12967]
    centre_nonneg := (scalarRow12967.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12967])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12967
/-! Actual 12968 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12968
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12968 ≤ (1.035434030464 : ℝ) := by
  have hr : (113.877126763894 : ℝ) ≤ √(12968 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.877126763894 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12968 12968 (11 / 1000) ≤
    (0.008394020646 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12968) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.877126763894 : ℝ) ≤ √(12968 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12968)
  have hdiv : K / √(12968 : ℝ) ≤ K / 113.877126763894 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.877126763894 ≤ (0.008394020646 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12968.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12968 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12968 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12968 := gPlus_lower 12968
end BstLean.Part269.N12968

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12968
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035434030463 : ℝ) ≤ wn 12968 := by
  have hn : √(12968 : ℝ) ≤ 113.877126763895 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12968 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.877126763895 ≤ 2 / √(12968 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246586084 : ℝ) ≤ rhoBar 12968 BstLean.Part154.csC ∧
    rhoBar 12968 BstLean.Part154.csC ≤ 0.000246586466 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035434030463 : ℝ) / (1.295212 * 12968) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035434030464 : ℝ) / (1.29521 * 12968) := by gcongr
      _ ≤ (0.000246586466 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12968 BstLean.Part154.csC) ≤ 0.000986406669 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12968 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12968 BstLean.Part154.csC) (piBar (rhoBar 12968 BstLean.Part154.csC)) ≤ 0.000188344222 ∧
    cc1 (rhoBar 12968 BstLean.Part154.csC) (piBar (rhoBar 12968 BstLean.Part154.csC)) ≤ 0.000119844717 ∧
    cc2 (rhoBar 12968 BstLean.Part154.csC) ≤ 0.000069570822 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12968 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12968 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12968 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12968 BstLean.Part154.csC * nuR (rhoBar 12968 BstLean.Part154.csC)) ≤ 0.000493188134 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246586466 : ℝ) * 0.000986406669 := by gcongr
      _ ≤ (0.000493188134 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12968 BstLean.Part154.csC) * nuR (rhoBar 12968 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000986406669 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12968 BstLean.Part154.csC) * rhoBar 12968 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246586466 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246586466 / 2 + 0.399 * 0.000986406669 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188344222 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493188134 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119844717 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246586466 / 1.414213562 := by gcongr
      _ ≤ (0.000069570822 : ℝ) := by norm_num

end BstLean.Part269.N12968

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12968
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12968 BstLean.Part154.csC) (piBar (rhoBar 12968 BstLean.Part154.csC)) ≤ 1.53194E-7 := by
  have hr0 : 0 ≤ rhoBar 12968 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12968 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12968 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12968 BstLean.Part154.csC) (piBar (rhoBar 12968 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12968 BstLean.Part154.csC) (piBar (rhoBar 12968 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12968 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188344222 : ℝ) ^ 2 + 0.000119844717 ^ 2 + 3 * 0.000069570822 ^ 2 +
        2 * 0.797885 * 0.000188344222 * 0.000119844717 + 2 * 0.000188344222 * 0.000069570822 +
        4 * 0.797885 * 0.000119844717 * 0.000069570822 := by gcongr
    _ ≤ (1.53194E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12968 BstLean.Part154.csC Θ ≤ 0.002573093799 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12968 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12968 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12968 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12968 BstLean.Part154.csC) (piBar (rhoBar 12968 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12968 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035434030464 * 1.53194E-7 / (0.000246586084 : ℝ) := by gcongr
    _ ≤ 0.002573093799 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12968 BstLean.Part154.csC Θ ≤ 0.002853940276 + 0.000650177410 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12968 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12968 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12968 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035434030464 : ℝ) * ((2 * Θ * 0.000246586466 +
        (6863 / 10000) * 0.000246586466 * 12968 * 0.000986406669) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002853940276 + 0.000650177410 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12968 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12968 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12968 0.011 Θ ∧ gammaRatio 12968 0.011 Θ ≤ 0.000084770051 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12968 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035434030464 : ℝ) * 0.525 / ((1 - 0.011) * 12968) := by gcongr
      _ ≤ (0.000084770051 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12968 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12968 0.011 Θ) :=
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
    badAllowance 12968 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12968 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12968 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12968 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12968 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12968 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12968 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12968 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12968 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12968 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12968 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035434030464 : ℝ) * 12968 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12968 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003275296753 + 0.003223271209 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12968

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12968
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12968 BstLean.Part154.csC) (piBar (rhoBar 12968 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12968 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12968 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12968 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12968 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12968 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12968 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12968 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12968 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12968 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12968 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12968 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12968 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12968 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12968 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051933304385 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12968) ≤ 0.010487071592 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12968 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035434030464)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010487071592 + 2 * 0.737676 / 12968) := by gcongr
    _ ≤ (0.051933304385 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12968 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12968

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12968
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515437577 : ℝ) ≤ plow 12968 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12968) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052474114138)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350874245) : eMP 12968 0.011 xi bn ≤ 0.001163330177 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12968 : ℝ) * (1 - 0.011))) ≤ 0.000575238274 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001350874245 / (12968 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575238274 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575238274 : ℝ) + 3.141593 * 0.052474114138 / (12968 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001163330177 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052474114138)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350874245) : PiBarMP 12968 12 0.011 xi bn ≤ 0.159559504380 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12968 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036754241184 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.249070636363 : ℝ) ≤ √((12968 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.877126763894 : ℝ) ≤ √(12968 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12968) ≤ 0.122345976393 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036754241184 + 0.052474114138 * 1.772454 / (2 * (113.249070636363 : ℝ))) * (1 + 0.001163330177) +
        8 / (12968 * 113.877126763894) + 0.122345976393 := by gcongr
    _ ≤ (0.159559504380 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052474114138)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350874245) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281005594587) :
    parallelOracle 12968 0.011 xi bn cd ≤ 0.160529279374 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12968 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12968 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515437577 : ℝ) ≤ plow 12968 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.877126763894 : ℝ) ≤ √(12968 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281005594587 : ℝ) / (2 * 0.560515437577 * 113.877126763894)) * 0.159559504380 +
        0.281005594587 ^ 2 / (2 * 0.560515437577 * 113.877126763894) := by gcongr
    _ ≤ (0.160529279374 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052474114138) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350874245)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281005594587) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12968 12968 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515437577 : ℝ) ≤ plow 12968 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.877126763894 : ℝ) ≤ √(12968 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12968 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12968 Θ 1.22 ≤ 0.011645011933 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.877126763894 := by gcongr <;> linarith
      _ ≤ (0.011645011933 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12968 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12968 12968 0.011 ≤ 0.008394020646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12968 12968 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12968 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12968 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12968 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12968 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160529279374 + 0.011645011933 + (0.008394020646 : ℝ) *
        (1 + 2 * (0.281005594587 + 0.011645011933) / (0.560515437577 * 113.877126763894))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12968]

end BstLean.Part269.N12968

/-! The original eight local profiles supply actual 12968 moment certificates. -/
namespace BstLean.Part269.N12968
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12968 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12968 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12968 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052474114138 ∧
    0 ≤ bN 12968 BstLean.Part154.csC (groupTheta g) ∧ bN 12968 BstLean.Part154.csC (groupTheta g) ≤ 0.001350874245 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12968 12968 0.011
      (momentAllowance 12968 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12968 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12968 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12968 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12968 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12968 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229072290202 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12968 0.011
      (momentAllowance 12968 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12968 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12968
/-! The actual computed-centre upper energy formula at 12968. -/
namespace BstLean.Part269.N12968
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12968

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12968
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12968)
open BstLean.Part268 (cell12968)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084744377414
  | 2 => 0.085674195865
  | 3 => 0.086600395105
  | 4 => 0.087523979715
  | 5 => 0.088446177031
  | 6 => 0.089368471750
  | 7 => 0.090292644097
  | 8 => 0.091220811615
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12968 12968 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12968 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12968

/-! Actual upper energy certificates on all 43 source endpoints at 12968. -/
namespace BstLean.Part269.N12968
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12968)
open BstLean.Part268 (cell12968)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12968 (gMinus 12968) (1 - (cell12968 i).lower) ≤ 1 ∧
    energyUpper 12968 (gMinus 12968) (BstLean.Part211.gPlus 12968)
      (finiteEnergy 12968 12968 0.011) (1 - (cell12968 i).lower) ≤
      (cell12968 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨10,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨11,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨12,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨13,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨14,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨15,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨16,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨17,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨18,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨19,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨20,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨21,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨22,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨23,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨24,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨25,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨26,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨27,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨28,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨29,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨30,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨31,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨32,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨33,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨34,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨35,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨36,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨37,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨38,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨39,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨40,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨41,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨42,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨43,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨44,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨45,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨46,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨47,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨48,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨49,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨50,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨51,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12968) (by norm_num)
        (q := 1 - (cell12968 ⟨52,by decide⟩).lower)
        (by norm_num [cell12968]) (by norm_num [cell12968])
      exact ⟨E.1,E.2.trans (by norm_num [cell12968])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12968

/-! Source-cell containment and simple scalar guards at 12968. -/
namespace BstLean.Part269.N12968
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12968)
open BstLean.Part268 (cell12968)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12968 ⟨10,by decide⟩).lower ∧ (cell12968 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12968 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12968 ⟨11,by decide⟩).lower ∧ (cell12968 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12968 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12968 ⟨12,by decide⟩).lower ∧ (cell12968 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12968 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12968 ⟨13,by decide⟩).lower ∧ (cell12968 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12968 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12968 ⟨14,by decide⟩).lower ∧ (cell12968 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12968 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12968 ⟨15,by decide⟩).lower ∧ (cell12968 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12968 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12968 ⟨16,by decide⟩).lower ∧ (cell12968 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12968 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12968 ⟨17,by decide⟩).lower ∧ (cell12968 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12968 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12968 ⟨18,by decide⟩).lower ∧ (cell12968 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12968 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12968 ⟨19,by decide⟩).lower ∧ (cell12968 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12968 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12968 ⟨20,by decide⟩).lower ∧ (cell12968 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12968 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12968 ⟨21,by decide⟩).lower ∧ (cell12968 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12968 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12968 ⟨22,by decide⟩).lower ∧ (cell12968 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12968 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12968 ⟨23,by decide⟩).lower ∧ (cell12968 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12968 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12968 ⟨24,by decide⟩).lower ∧ (cell12968 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12968 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12968 ⟨25,by decide⟩).lower ∧ (cell12968 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12968 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12968 ⟨26,by decide⟩).lower ∧ (cell12968 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12968 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12968 ⟨27,by decide⟩).lower ∧ (cell12968 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12968 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12968 ⟨28,by decide⟩).lower ∧ (cell12968 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12968 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12968 ⟨29,by decide⟩).lower ∧ (cell12968 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12968 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12968 ⟨30,by decide⟩).lower ∧ (cell12968 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12968 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12968 ⟨31,by decide⟩).lower ∧ (cell12968 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12968 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12968 ⟨32,by decide⟩).lower ∧ (cell12968 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12968 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12968 ⟨33,by decide⟩).lower ∧ (cell12968 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12968 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12968 ⟨34,by decide⟩).lower ∧ (cell12968 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12968 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12968 ⟨35,by decide⟩).lower ∧ (cell12968 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12968 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12968 ⟨36,by decide⟩).lower ∧ (cell12968 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12968 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12968 ⟨37,by decide⟩).lower ∧ (cell12968 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12968 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12968 ⟨38,by decide⟩).lower ∧ (cell12968 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12968 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12968 ⟨39,by decide⟩).lower ∧ (cell12968 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12968 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12968 ⟨40,by decide⟩).lower ∧ (cell12968 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12968 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12968 ⟨41,by decide⟩).lower ∧ (cell12968 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12968 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12968 ⟨42,by decide⟩).lower ∧ (cell12968 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12968 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12968 ⟨43,by decide⟩).lower ∧ (cell12968 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12968 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12968 ⟨44,by decide⟩).lower ∧ (cell12968 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12968 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12968 ⟨45,by decide⟩).lower ∧ (cell12968 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12968 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12968 ⟨46,by decide⟩).lower ∧ (cell12968 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12968 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12968 ⟨47,by decide⟩).lower ∧ (cell12968 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12968 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12968 ⟨48,by decide⟩).lower ∧ (cell12968 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12968 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12968 ⟨49,by decide⟩).lower ∧ (cell12968 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12968 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12968 ⟨50,by decide⟩).lower ∧ (cell12968 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12968 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12968 ⟨51,by decide⟩).lower ∧ (cell12968 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12968 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12968 ⟨52,by decide⟩).lower ∧ (cell12968 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12968 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12968 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12968 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12968,cell12968,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12968 i).lower ∧
    (cell12968 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12968 i).upper ≤ (0.532 : ℝ) ∧
    (cell12968 i).centre ≤ (0.1 : ℝ) ∧ (cell12968 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12968 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12968 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12968

/-! The local source numeric instances at 12968 have no network premises. -/
namespace BstLean.Part269.N12968
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12968)
open BstLean.Part268 (cell12968)

noncomputable def sourceNumerics12968 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12968 (cell12968 i)
      scalarRow12968.M scalarRow12968.H scalarRow12968.xi := by
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
    energy_allowance := scalarRow12968.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12968]
    centre_nonneg := (scalarRow12968.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12968])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12968
/-! Actual 12969 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12969
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12969 ≤ (1.035432652441 : ℝ) := by
  have hr : (113.881517376613 : ℝ) ≤ √(12969 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.881517376613 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12969 12969 (11 / 1000) ≤
    (0.008393697019 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12969) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.881517376613 : ℝ) ≤ √(12969 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12969)
  have hdiv : K / √(12969 : ℝ) ≤ K / 113.881517376613 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.881517376613 ≤ (0.008393697019 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12969.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12969 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12969 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12969 := gPlus_lower 12969
end BstLean.Part269.N12969

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12969
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035432652440 : ℝ) ≤ wn 12969 := by
  have hn : √(12969 : ℝ) ≤ 113.881517376614 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12969 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.881517376614 ≤ 2 / √(12969 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246566742 : ℝ) ≤ rhoBar 12969 BstLean.Part154.csC ∧
    rhoBar 12969 BstLean.Part154.csC ≤ 0.000246567124 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035432652440 : ℝ) / (1.295212 * 12969) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035432652441 : ℝ) / (1.29521 * 12969) := by gcongr
      _ ≤ (0.000246567124 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12969 BstLean.Part154.csC) ≤ 0.000986329292 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12969 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12969 BstLean.Part154.csC) (piBar (rhoBar 12969 BstLean.Part154.csC)) ≤ 0.000188329448 ∧
    cc1 (rhoBar 12969 BstLean.Part154.csC) (piBar (rhoBar 12969 BstLean.Part154.csC)) ≤ 0.000119835316 ∧
    cc2 (rhoBar 12969 BstLean.Part154.csC) ≤ 0.000069565365 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12969 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12969 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12969 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12969 BstLean.Part154.csC * nuR (rhoBar 12969 BstLean.Part154.csC)) ≤ 0.000493149447 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246567124 : ℝ) * 0.000986329292 := by gcongr
      _ ≤ (0.000493149447 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12969 BstLean.Part154.csC) * nuR (rhoBar 12969 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000986329292 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12969 BstLean.Part154.csC) * rhoBar 12969 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246567124 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246567124 / 2 + 0.399 * 0.000986329292 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188329448 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493149447 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119835316 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246567124 / 1.414213562 := by gcongr
      _ ≤ (0.000069565365 : ℝ) := by norm_num

end BstLean.Part269.N12969

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12969
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12969 BstLean.Part154.csC) (piBar (rhoBar 12969 BstLean.Part154.csC)) ≤ 1.53169E-7 := by
  have hr0 : 0 ≤ rhoBar 12969 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12969 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12969 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12969 BstLean.Part154.csC) (piBar (rhoBar 12969 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12969 BstLean.Part154.csC) (piBar (rhoBar 12969 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12969 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188329448 : ℝ) ^ 2 + 0.000119835316 ^ 2 + 3 * 0.000069565365 ^ 2 +
        2 * 0.797885 * 0.000188329448 * 0.000119835316 + 2 * 0.000188329448 * 0.000069565365 +
        4 * 0.797885 * 0.000119835316 * 0.000069565365 := by gcongr
    _ ≤ (1.53169E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12969 BstLean.Part154.csC Θ ≤ 0.002572872281 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12969 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12969 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12969 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12969 BstLean.Part154.csC) (piBar (rhoBar 12969 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12969 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035432652441 * 1.53169E-7 / (0.000246566742 : ℝ) := by gcongr
    _ ≤ 0.002572872281 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12969 BstLean.Part154.csC Θ ≤ 0.002853708804 + 0.000650125545 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12969 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12969 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12969 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035432652441 : ℝ) * ((2 * Θ * 0.000246567124 +
        (6863 / 10000) * 0.000246567124 * 12969 * 0.000986329292) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002853708804 + 0.000650125545 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12969 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12969 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12969 0.011 Θ ∧ gammaRatio 12969 0.011 Θ ≤ 0.000084763401 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12969 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035432652441 : ℝ) * 0.525 / ((1 - 0.011) * 12969) := by gcongr
      _ ≤ (0.000084763401 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12969 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12969 0.011 Θ) :=
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
    badAllowance 12969 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12969 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12969 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12969 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12969 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12969 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12969 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12969 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12969 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12969 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12969 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035432652441 : ℝ) * 12969 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12969 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003275065281 + 0.003222997826 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12969

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12969
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12969 BstLean.Part154.csC) (piBar (rhoBar 12969 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12969 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12969 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12969 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12969 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12969 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12969 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12969 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12969 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12969 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12969 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12969 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12969 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12969 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12969 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051931280654 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12969) ≤ 0.010486667272 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12969 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035432652441)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010486667272 + 2 * 0.737676 / 12969) := by gcongr
    _ ≤ (0.051931280654 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12969 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12969

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12969
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515480946 : ℝ) ≤ plow 12969 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12969) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052473739140)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350757948) : eMP 12969 0.011 xi bn ≤ 0.001163235218 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12969 : ℝ) * (1 - 0.011))) ≤ 0.000575191336 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001350757948 / (12969 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575191336 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575191336 : ℝ) + 3.141593 * 0.052473739140 / (12969 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001163235218 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052473739140)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350757948) : PiBarMP 12969 12 0.011 xi bn ≤ 0.159553180520 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12969 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036752659061 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.253437033937 : ℝ) ≤ √((12969 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.881517376613 : ℝ) ≤ √(12969 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12969) ≤ 0.122341259440 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036752659061 + 0.052473739140 * 1.772454 / (2 * (113.253437033937 : ℝ))) * (1 + 0.001163235218) +
        8 / (12969 * 113.881517376613) + 0.122341259440 := by gcongr
    _ ≤ (0.159553180520 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052473739140)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350757948) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281002752340) :
    parallelOracle 12969 0.011 xi bn cd ≤ 0.160522888066 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12969 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12969 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515480946 : ℝ) ≤ plow 12969 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.881517376613 : ℝ) ≤ √(12969 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281002752340 : ℝ) / (2 * 0.560515480946 * 113.881517376613)) * 0.159553180520 +
        0.281002752340 ^ 2 / (2 * 0.560515480946 * 113.881517376613) := by gcongr
    _ ≤ (0.160522888066 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052473739140) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350757948)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281002752340) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12969 12969 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515480946 : ℝ) ≤ plow 12969 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.881517376613 : ℝ) ≤ √(12969 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12969 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12969 Θ 1.22 ≤ 0.011644562969 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.881517376613 := by gcongr <;> linarith
      _ ≤ (0.011644562969 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12969 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12969 12969 0.011 ≤ 0.008393697019 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12969 12969 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12969 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12969 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12969 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12969 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160522888066 + 0.011644562969 + (0.008393697019 : ℝ) *
        (1 + 2 * (0.281002752340 + 0.011644562969) / (0.560515480946 * 113.881517376613))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12969]

end BstLean.Part269.N12969

/-! The original eight local profiles supply actual 12969 moment certificates. -/
namespace BstLean.Part269.N12969
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12969 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12969 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12969 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052473739140 ∧
    0 ≤ bN 12969 BstLean.Part154.csC (groupTheta g) ∧ bN 12969 BstLean.Part154.csC (groupTheta g) ≤ 0.001350757948 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12969 12969 0.011
      (momentAllowance 12969 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12969 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12969 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12969 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12969 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12969 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229071471686 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12969 0.011
      (momentAllowance 12969 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12969 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12969
/-! The actual computed-centre upper energy formula at 12969. -/
namespace BstLean.Part269.N12969
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12969

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12969
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12969)
open BstLean.Part268 (cell12969)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084741716769
  | 2 => 0.085671491738
  | 3 => 0.086597642054
  | 4 => 0.087521170989
  | 5 => 0.088443304328
  | 6 => 0.089365524947
  | 7 => 0.090289610941
  | 8 => 0.091217677381
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12969 12969 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12969 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12969

/-! Actual upper energy certificates on all 43 source endpoints at 12969. -/
namespace BstLean.Part269.N12969
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12969)
open BstLean.Part268 (cell12969)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12969 (gMinus 12969) (1 - (cell12969 i).lower) ≤ 1 ∧
    energyUpper 12969 (gMinus 12969) (BstLean.Part211.gPlus 12969)
      (finiteEnergy 12969 12969 0.011) (1 - (cell12969 i).lower) ≤
      (cell12969 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨10,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨11,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨12,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨13,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨14,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨15,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨16,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨17,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨18,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨19,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨20,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨21,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨22,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨23,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨24,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨25,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨26,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨27,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨28,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨29,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨30,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨31,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨32,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨33,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨34,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨35,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨36,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨37,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨38,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨39,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨40,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨41,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨42,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨43,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨44,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨45,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨46,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨47,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨48,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨49,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨50,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨51,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12969) (by norm_num)
        (q := 1 - (cell12969 ⟨52,by decide⟩).lower)
        (by norm_num [cell12969]) (by norm_num [cell12969])
      exact ⟨E.1,E.2.trans (by norm_num [cell12969])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12969

/-! Source-cell containment and simple scalar guards at 12969. -/
namespace BstLean.Part269.N12969
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12969)
open BstLean.Part268 (cell12969)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12969 ⟨10,by decide⟩).lower ∧ (cell12969 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12969 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12969 ⟨11,by decide⟩).lower ∧ (cell12969 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12969 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12969 ⟨12,by decide⟩).lower ∧ (cell12969 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12969 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12969 ⟨13,by decide⟩).lower ∧ (cell12969 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12969 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12969 ⟨14,by decide⟩).lower ∧ (cell12969 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12969 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12969 ⟨15,by decide⟩).lower ∧ (cell12969 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12969 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12969 ⟨16,by decide⟩).lower ∧ (cell12969 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12969 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12969 ⟨17,by decide⟩).lower ∧ (cell12969 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12969 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12969 ⟨18,by decide⟩).lower ∧ (cell12969 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12969 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12969 ⟨19,by decide⟩).lower ∧ (cell12969 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12969 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12969 ⟨20,by decide⟩).lower ∧ (cell12969 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12969 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12969 ⟨21,by decide⟩).lower ∧ (cell12969 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12969 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12969 ⟨22,by decide⟩).lower ∧ (cell12969 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12969 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12969 ⟨23,by decide⟩).lower ∧ (cell12969 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12969 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12969 ⟨24,by decide⟩).lower ∧ (cell12969 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12969 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12969 ⟨25,by decide⟩).lower ∧ (cell12969 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12969 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12969 ⟨26,by decide⟩).lower ∧ (cell12969 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12969 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12969 ⟨27,by decide⟩).lower ∧ (cell12969 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12969 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12969 ⟨28,by decide⟩).lower ∧ (cell12969 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12969 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12969 ⟨29,by decide⟩).lower ∧ (cell12969 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12969 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12969 ⟨30,by decide⟩).lower ∧ (cell12969 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12969 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12969 ⟨31,by decide⟩).lower ∧ (cell12969 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12969 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12969 ⟨32,by decide⟩).lower ∧ (cell12969 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12969 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12969 ⟨33,by decide⟩).lower ∧ (cell12969 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12969 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12969 ⟨34,by decide⟩).lower ∧ (cell12969 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12969 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12969 ⟨35,by decide⟩).lower ∧ (cell12969 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12969 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12969 ⟨36,by decide⟩).lower ∧ (cell12969 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12969 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12969 ⟨37,by decide⟩).lower ∧ (cell12969 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12969 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12969 ⟨38,by decide⟩).lower ∧ (cell12969 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12969 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12969 ⟨39,by decide⟩).lower ∧ (cell12969 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12969 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12969 ⟨40,by decide⟩).lower ∧ (cell12969 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12969 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12969 ⟨41,by decide⟩).lower ∧ (cell12969 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12969 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12969 ⟨42,by decide⟩).lower ∧ (cell12969 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12969 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12969 ⟨43,by decide⟩).lower ∧ (cell12969 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12969 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12969 ⟨44,by decide⟩).lower ∧ (cell12969 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12969 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12969 ⟨45,by decide⟩).lower ∧ (cell12969 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12969 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12969 ⟨46,by decide⟩).lower ∧ (cell12969 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12969 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12969 ⟨47,by decide⟩).lower ∧ (cell12969 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12969 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12969 ⟨48,by decide⟩).lower ∧ (cell12969 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12969 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12969 ⟨49,by decide⟩).lower ∧ (cell12969 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12969 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12969 ⟨50,by decide⟩).lower ∧ (cell12969 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12969 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12969 ⟨51,by decide⟩).lower ∧ (cell12969 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12969 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12969 ⟨52,by decide⟩).lower ∧ (cell12969 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12969 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12969 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12969 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12969,cell12969,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12969 i).lower ∧
    (cell12969 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12969 i).upper ≤ (0.532 : ℝ) ∧
    (cell12969 i).centre ≤ (0.1 : ℝ) ∧ (cell12969 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12969 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12969 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12969

/-! The local source numeric instances at 12969 have no network premises. -/
namespace BstLean.Part269.N12969
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12969)
open BstLean.Part268 (cell12969)

noncomputable def sourceNumerics12969 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12969 (cell12969 i)
      scalarRow12969.M scalarRow12969.H scalarRow12969.xi := by
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
    energy_allowance := scalarRow12969.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12969]
    centre_nonneg := (scalarRow12969.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12969])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12969
/-! Actual 12970 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12970
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12970 ≤ (1.035431274579 : ℝ) := by
  have hr : (113.885907820063 : ℝ) ≤ √(12970 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.885907820063 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12970 12970 (11 / 1000) ≤
    (0.008393373429 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12970) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.885907820063 : ℝ) ≤ √(12970 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12970)
  have hdiv : K / √(12970 : ℝ) ≤ K / 113.885907820063 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.885907820063 ≤ (0.008393373429 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12970.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12970 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12970 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12970 := gPlus_lower 12970
end BstLean.Part269.N12970

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12970
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035431274578 : ℝ) ≤ wn 12970 := by
  have hn : √(12970 : ℝ) ≤ 113.885907820064 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12970 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.885907820064 ≤ 2 / √(12970 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246547404 : ℝ) ≤ rhoBar 12970 BstLean.Part154.csC ∧
    rhoBar 12970 BstLean.Part154.csC ≤ 0.000246547785 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035431274578 : ℝ) / (1.295212 * 12970) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035431274579 : ℝ) / (1.29521 * 12970) := by gcongr
      _ ≤ (0.000246547785 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12970 BstLean.Part154.csC) ≤ 0.000986251926 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12970 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12970 BstLean.Part154.csC) (piBar (rhoBar 12970 BstLean.Part154.csC)) ≤ 0.000188314676 ∧
    cc1 (rhoBar 12970 BstLean.Part154.csC) (piBar (rhoBar 12970 BstLean.Part154.csC)) ≤ 0.000119825917 ∧
    cc2 (rhoBar 12970 BstLean.Part154.csC) ≤ 0.000069559909 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12970 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12970 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12970 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12970 BstLean.Part154.csC * nuR (rhoBar 12970 BstLean.Part154.csC)) ≤ 0.000493110767 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246547785 : ℝ) * 0.000986251926 := by gcongr
      _ ≤ (0.000493110767 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12970 BstLean.Part154.csC) * nuR (rhoBar 12970 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000986251926 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12970 BstLean.Part154.csC) * rhoBar 12970 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246547785 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246547785 / 2 + 0.399 * 0.000986251926 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188314676 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493110767 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119825917 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246547785 / 1.414213562 := by gcongr
      _ ≤ (0.000069559909 : ℝ) := by norm_num

end BstLean.Part269.N12970

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12970
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12970 BstLean.Part154.csC) (piBar (rhoBar 12970 BstLean.Part154.csC)) ≤ 1.53145E-7 := by
  have hr0 : 0 ≤ rhoBar 12970 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12970 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12970 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12970 BstLean.Part154.csC) (piBar (rhoBar 12970 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12970 BstLean.Part154.csC) (piBar (rhoBar 12970 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12970 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188314676 : ℝ) ^ 2 + 0.000119825917 ^ 2 + 3 * 0.000069559909 ^ 2 +
        2 * 0.797885 * 0.000188314676 * 0.000119825917 + 2 * 0.000188314676 * 0.000069559909 +
        4 * 0.797885 * 0.000119825917 * 0.000069559909 := by gcongr
    _ ≤ (1.53145E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12970 BstLean.Part154.csC Θ ≤ 0.002572667487 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12970 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12970 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12970 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12970 BstLean.Part154.csC) (piBar (rhoBar 12970 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12970 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035431274579 * 1.53145E-7 / (0.000246547404 : ℝ) := by gcongr
    _ ≤ 0.002572667487 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12970 BstLean.Part154.csC Θ ≤ 0.002853477366 + 0.000650073689 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12970 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12970 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12970 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035431274579 : ℝ) * ((2 * Θ * 0.000246547785 +
        (6863 / 10000) * 0.000246547785 * 12970 * 0.000986251926) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002853477366 + 0.000650073689 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12970 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12970 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12970 0.011 Θ ∧ gammaRatio 12970 0.011 Θ ≤ 0.000084756753 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12970 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035431274579 : ℝ) * 0.525 / ((1 - 0.011) * 12970) := by gcongr
      _ ≤ (0.000084756753 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12970 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12970 0.011 Θ) :=
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
    badAllowance 12970 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12970 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12970 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12970 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12970 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12970 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12970 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12970 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12970 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12970 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12970 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035431274579 : ℝ) * 12970 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12970 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003274833843 + 0.003222741176 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12970

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12970
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12970 BstLean.Part154.csC) (piBar (rhoBar 12970 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12970 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12970 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12970 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12970 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12970 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12970 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12970 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12970 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12970 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12970 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12970 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12970 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12970 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12970 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051929257149 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12970) ≤ 0.010486262997 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12970 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035431274579)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010486262997 + 2 * 0.737676 / 12970) := by gcongr
    _ ≤ (0.051929257149 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12970 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12970

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12970
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515524309 : ℝ) ≤ plow 12970 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12970) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052473372961)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350650431) : eMP 12970 0.011 xi bn ≤ 0.001163144005 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12970 : ℝ) * (1 - 0.011))) ≤ 0.000575146270 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001350650431 / (12970 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575146270 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575146270 : ℝ) + 3.141593 * 0.052473372961 / (12970 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001163144005 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052473372961)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350650431) : PiBarMP 12970 12 0.011 xi bn ≤ 0.159546976938 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12970 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036751196321 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.257803263174 : ℝ) ≤ √((12970 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.885907820063 : ℝ) ≤ √(12970 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12970) ≤ 0.122336543032 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036751196321 + 0.052473372961 * 1.772454 / (2 * (113.257803263174 : ℝ))) * (1 + 0.001163144005) +
        8 / (12970 * 113.885907820063) + 0.122336543032 := by gcongr
    _ ≤ (0.159546976938 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052473372961)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350650431) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280999929565) :
    parallelOracle 12970 0.011 xi bn cd ≤ 0.160516617418 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12970 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12970 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515524309 : ℝ) ≤ plow 12970 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.885907820063 : ℝ) ≤ √(12970 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280999929565 : ℝ) / (2 * 0.560515524309 * 113.885907820063)) * 0.159546976938 +
        0.280999929565 ^ 2 / (2 * 0.560515524309 * 113.885907820063) := by gcongr
    _ ≤ (0.160516617418 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052473372961) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350650431)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280999929565) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12970 12970 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515524309 : ℝ) ≤ plow 12970 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.885907820063 : ℝ) ≤ √(12970 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12970 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12970 Θ 1.22 ≤ 0.011644114056 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.885907820063 := by gcongr <;> linarith
      _ ≤ (0.011644114056 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12970 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12970 12970 0.011 ≤ 0.008393373429 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12970 12970 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12970 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12970 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12970 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12970 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160516617418 + 0.011644114056 + (0.008393373429 : ℝ) *
        (1 + 2 * (0.280999929565 + 0.011644114056) / (0.560515524309 * 113.885907820063))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12970]

end BstLean.Part269.N12970

/-! The original eight local profiles supply actual 12970 moment certificates. -/
namespace BstLean.Part269.N12970
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12970 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12970 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12970 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052473372961 ∧
    0 ≤ bN 12970 BstLean.Part154.csC (groupTheta g) ∧ bN 12970 BstLean.Part154.csC (groupTheta g) ≤ 0.001350650431 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12970 12970 0.011
      (momentAllowance 12970 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12970 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12970 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12970 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12970 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12970 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229070672416 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12970 0.011
      (momentAllowance 12970 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12970 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12970
/-! The actual computed-centre upper energy formula at 12970. -/
namespace BstLean.Part269.N12970
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12970

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12970
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12970)
open BstLean.Part268 (cell12970)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084739056959
  | 2 => 0.085668788477
  | 3 => 0.086594889908
  | 4 => 0.087518363215
  | 5 => 0.088440432636
  | 6 => 0.089362579227
  | 7 => 0.090286578954
  | 8 => 0.091214544421
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12970 12970 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12970 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12970

/-! Actual upper energy certificates on all 43 source endpoints at 12970. -/
namespace BstLean.Part269.N12970
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12970)
open BstLean.Part268 (cell12970)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12970 (gMinus 12970) (1 - (cell12970 i).lower) ≤ 1 ∧
    energyUpper 12970 (gMinus 12970) (BstLean.Part211.gPlus 12970)
      (finiteEnergy 12970 12970 0.011) (1 - (cell12970 i).lower) ≤
      (cell12970 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨10,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨11,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨12,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨13,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨14,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨15,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨16,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨17,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨18,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨19,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨20,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨21,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨22,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨23,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨24,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨25,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨26,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨27,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨28,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨29,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨30,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨31,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨32,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨33,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨34,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨35,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨36,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨37,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨38,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨39,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨40,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨41,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨42,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨43,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨44,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨45,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨46,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨47,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨48,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨49,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨50,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨51,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12970) (by norm_num)
        (q := 1 - (cell12970 ⟨52,by decide⟩).lower)
        (by norm_num [cell12970]) (by norm_num [cell12970])
      exact ⟨E.1,E.2.trans (by norm_num [cell12970])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12970

/-! Source-cell containment and simple scalar guards at 12970. -/
namespace BstLean.Part269.N12970
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12970)
open BstLean.Part268 (cell12970)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12970 ⟨10,by decide⟩).lower ∧ (cell12970 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12970 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12970 ⟨11,by decide⟩).lower ∧ (cell12970 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12970 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12970 ⟨12,by decide⟩).lower ∧ (cell12970 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12970 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12970 ⟨13,by decide⟩).lower ∧ (cell12970 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12970 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12970 ⟨14,by decide⟩).lower ∧ (cell12970 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12970 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12970 ⟨15,by decide⟩).lower ∧ (cell12970 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12970 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12970 ⟨16,by decide⟩).lower ∧ (cell12970 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12970 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12970 ⟨17,by decide⟩).lower ∧ (cell12970 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12970 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12970 ⟨18,by decide⟩).lower ∧ (cell12970 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12970 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12970 ⟨19,by decide⟩).lower ∧ (cell12970 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12970 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12970 ⟨20,by decide⟩).lower ∧ (cell12970 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12970 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12970 ⟨21,by decide⟩).lower ∧ (cell12970 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12970 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12970 ⟨22,by decide⟩).lower ∧ (cell12970 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12970 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12970 ⟨23,by decide⟩).lower ∧ (cell12970 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12970 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12970 ⟨24,by decide⟩).lower ∧ (cell12970 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12970 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12970 ⟨25,by decide⟩).lower ∧ (cell12970 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12970 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12970 ⟨26,by decide⟩).lower ∧ (cell12970 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12970 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12970 ⟨27,by decide⟩).lower ∧ (cell12970 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12970 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12970 ⟨28,by decide⟩).lower ∧ (cell12970 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12970 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12970 ⟨29,by decide⟩).lower ∧ (cell12970 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12970 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12970 ⟨30,by decide⟩).lower ∧ (cell12970 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12970 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12970 ⟨31,by decide⟩).lower ∧ (cell12970 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12970 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12970 ⟨32,by decide⟩).lower ∧ (cell12970 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12970 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12970 ⟨33,by decide⟩).lower ∧ (cell12970 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12970 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12970 ⟨34,by decide⟩).lower ∧ (cell12970 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12970 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12970 ⟨35,by decide⟩).lower ∧ (cell12970 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12970 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12970 ⟨36,by decide⟩).lower ∧ (cell12970 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12970 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12970 ⟨37,by decide⟩).lower ∧ (cell12970 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12970 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12970 ⟨38,by decide⟩).lower ∧ (cell12970 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12970 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12970 ⟨39,by decide⟩).lower ∧ (cell12970 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12970 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12970 ⟨40,by decide⟩).lower ∧ (cell12970 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12970 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12970 ⟨41,by decide⟩).lower ∧ (cell12970 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12970 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12970 ⟨42,by decide⟩).lower ∧ (cell12970 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12970 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12970 ⟨43,by decide⟩).lower ∧ (cell12970 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12970 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12970 ⟨44,by decide⟩).lower ∧ (cell12970 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12970 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12970 ⟨45,by decide⟩).lower ∧ (cell12970 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12970 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12970 ⟨46,by decide⟩).lower ∧ (cell12970 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12970 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12970 ⟨47,by decide⟩).lower ∧ (cell12970 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12970 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12970 ⟨48,by decide⟩).lower ∧ (cell12970 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12970 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12970 ⟨49,by decide⟩).lower ∧ (cell12970 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12970 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12970 ⟨50,by decide⟩).lower ∧ (cell12970 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12970 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12970 ⟨51,by decide⟩).lower ∧ (cell12970 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12970 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12970 ⟨52,by decide⟩).lower ∧ (cell12970 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12970 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12970 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12970 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12970,cell12970,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12970 i).lower ∧
    (cell12970 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12970 i).upper ≤ (0.532 : ℝ) ∧
    (cell12970 i).centre ≤ (0.1 : ℝ) ∧ (cell12970 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12970 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12970 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12970

/-! The local source numeric instances at 12970 have no network premises. -/
namespace BstLean.Part269.N12970
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12970)
open BstLean.Part268 (cell12970)

noncomputable def sourceNumerics12970 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12970 (cell12970 i)
      scalarRow12970.M scalarRow12970.H scalarRow12970.xi := by
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
    energy_allowance := scalarRow12970.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12970]
    centre_nonneg := (scalarRow12970.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12970])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12970
/-! Actual 12971 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12971
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12971 ≤ (1.035429896876 : ℝ) := by
  have hr : (113.890298094262 : ℝ) ≤ √(12971 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.890298094262 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12971 12971 (11 / 1000) ≤
    (0.008393049876 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12971) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.890298094262 : ℝ) ≤ √(12971 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12971)
  have hdiv : K / √(12971 : ℝ) ≤ K / 113.890298094262 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.890298094262 ≤ (0.008393049876 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12971.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12971 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12971 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12971 := gPlus_lower 12971
end BstLean.Part269.N12971

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12971
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035429896875 : ℝ) ≤ wn 12971 := by
  have hn : √(12971 : ℝ) ≤ 113.890298094263 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12971 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.890298094263 ≤ 2 / √(12971 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246528068 : ℝ) ≤ rhoBar 12971 BstLean.Part154.csC ∧
    rhoBar 12971 BstLean.Part154.csC ≤ 0.000246528450 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035429896875 : ℝ) / (1.295212 * 12971) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035429896876 : ℝ) / (1.29521 * 12971) := by gcongr
      _ ≤ (0.000246528450 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12971 BstLean.Part154.csC) ≤ 0.000986174577 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12971 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12971 BstLean.Part154.csC) (piBar (rhoBar 12971 BstLean.Part154.csC)) ≤ 0.000188299907 ∧
    cc1 (rhoBar 12971 BstLean.Part154.csC) (piBar (rhoBar 12971 BstLean.Part154.csC)) ≤ 0.000119816520 ∧
    cc2 (rhoBar 12971 BstLean.Part154.csC) ≤ 0.000069554454 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12971 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12971 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12971 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12971 BstLean.Part154.csC * nuR (rhoBar 12971 BstLean.Part154.csC)) ≤ 0.000493072095 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246528450 : ℝ) * 0.000986174577 := by gcongr
      _ ≤ (0.000493072095 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12971 BstLean.Part154.csC) * nuR (rhoBar 12971 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000986174577 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12971 BstLean.Part154.csC) * rhoBar 12971 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246528450 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246528450 / 2 + 0.399 * 0.000986174577 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188299907 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493072095 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119816520 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246528450 / 1.414213562 := by gcongr
      _ ≤ (0.000069554454 : ℝ) := by norm_num

end BstLean.Part269.N12971

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12971
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12971 BstLean.Part154.csC) (piBar (rhoBar 12971 BstLean.Part154.csC)) ≤ 1.53121E-7 := by
  have hr0 : 0 ≤ rhoBar 12971 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12971 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12971 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12971 BstLean.Part154.csC) (piBar (rhoBar 12971 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12971 BstLean.Part154.csC) (piBar (rhoBar 12971 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12971 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188299907 : ℝ) ^ 2 + 0.000119816520 ^ 2 + 3 * 0.000069554454 ^ 2 +
        2 * 0.797885 * 0.000188299907 * 0.000119816520 + 2 * 0.000188299907 * 0.000069554454 +
        4 * 0.797885 * 0.000119816520 * 0.000069554454 := by gcongr
    _ ≤ (1.53121E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12971 BstLean.Part154.csC Θ ≤ 0.002572462642 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12971 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12971 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12971 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12971 BstLean.Part154.csC) (piBar (rhoBar 12971 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12971 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035429896876 * 1.53121E-7 / (0.000246528068 : ℝ) := by gcongr
    _ ≤ 0.002572462642 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12971 BstLean.Part154.csC Θ ≤ 0.002853245990 + 0.000650021843 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12971 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12971 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12971 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035429896876 : ℝ) * ((2 * Θ * 0.000246528450 +
        (6863 / 10000) * 0.000246528450 * 12971 * 0.000986174577) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002853245990 + 0.000650021843 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12971 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12971 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12971 0.011 Θ ∧ gammaRatio 12971 0.011 Θ ≤ 0.000084750106 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12971 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035429896876 : ℝ) * 0.525 / ((1 - 0.011) * 12971) := by gcongr
      _ ≤ (0.000084750106 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12971 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12971 0.011 Θ) :=
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
    badAllowance 12971 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12971 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12971 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12971 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12971 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12971 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12971 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12971 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12971 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12971 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12971 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035429896876 : ℝ) * 12971 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12971 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003274602467 + 0.003222484485 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12971

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12971
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12971 BstLean.Part154.csC) (piBar (rhoBar 12971 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12971 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12971 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12971 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12971 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12971 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12971 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12971 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12971 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12971 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12971 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12971 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12971 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12971 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12971 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051927233887 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12971) ≤ 0.010485858770 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12971 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035429896876)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010485858770 + 2 * 0.737676 / 12971) := by gcongr
    _ ≤ (0.051927233887 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12971 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12971

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12971
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515567666 : ℝ) ≤ plow 12971 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12971) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052473006822)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350542888) : eMP 12971 0.011 xi bn ≤ 0.001163052789 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12971 : ℝ) * (1 - 0.011))) ≤ 0.000575101202 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001350542888 / (12971 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575101202 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575101202 : ℝ) + 3.141593 * 0.052473006822 / (12971 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001163052789 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052473006822)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350542888) : PiBarMP 12971 12 0.011 xi bn ≤ 0.159540773492 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12971 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036749733170 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.262169324095 : ℝ) ≤ √((12971 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.890298094262 : ℝ) ≤ √(12971 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12971) ≤ 0.122331827170 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036749733170 + 0.052473006822 * 1.772454 / (2 * (113.262169324095 : ℝ))) * (1 + 0.001163052789) +
        8 / (12971 * 113.890298094262) + 0.122331827170 := by gcongr
    _ ≤ (0.159540773492 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052473006822)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350542888) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280997107118) :
    parallelOracle 12971 0.011 xi bn cd ≤ 0.160510346915 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12971 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12971 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515567666 : ℝ) ≤ plow 12971 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.890298094262 : ℝ) ≤ √(12971 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280997107118 : ℝ) / (2 * 0.560515567666 * 113.890298094262)) * 0.159540773492 +
        0.280997107118 ^ 2 / (2 * 0.560515567666 * 113.890298094262) := by gcongr
    _ ≤ (0.160510346915 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052473006822) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350542888)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280997107118) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12971 12971 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515567666 : ℝ) ≤ plow 12971 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.890298094262 : ℝ) ≤ √(12971 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12971 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12971 Θ 1.22 ≤ 0.011643665196 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.890298094262 := by gcongr <;> linarith
      _ ≤ (0.011643665196 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12971 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12971 12971 0.011 ≤ 0.008393049876 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12971 12971 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12971 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12971 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12971 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12971 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160510346915 + 0.011643665196 + (0.008393049876 : ℝ) *
        (1 + 2 * (0.280997107118 + 0.011643665196) / (0.560515567666 * 113.890298094262))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12971]

end BstLean.Part269.N12971

/-! The original eight local profiles supply actual 12971 moment certificates. -/
namespace BstLean.Part269.N12971
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12971 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12971 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12971 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052473006822 ∧
    0 ≤ bN 12971 BstLean.Part154.csC (groupTheta g) ∧ bN 12971 BstLean.Part154.csC (groupTheta g) ≤ 0.001350542888 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12971 12971 0.011
      (momentAllowance 12971 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12971 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12971 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12971 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12971 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12971 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229069873231 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12971 0.011
      (momentAllowance 12971 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12971 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12971
/-! The actual computed-centre upper energy formula at 12971. -/
namespace BstLean.Part269.N12971
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12971

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12971
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12971)
open BstLean.Part268 (cell12971)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084736397982
  | 2 => 0.085666086080
  | 3 => 0.086592138665
  | 4 => 0.087515556393
  | 5 => 0.088437561955
  | 6 => 0.089359634588
  | 7 => 0.090283548134
  | 8 => 0.091211412733
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12971 12971 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12971 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12971

/-! Actual upper energy certificates on all 43 source endpoints at 12971. -/
namespace BstLean.Part269.N12971
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12971)
open BstLean.Part268 (cell12971)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12971 (gMinus 12971) (1 - (cell12971 i).lower) ≤ 1 ∧
    energyUpper 12971 (gMinus 12971) (BstLean.Part211.gPlus 12971)
      (finiteEnergy 12971 12971 0.011) (1 - (cell12971 i).lower) ≤
      (cell12971 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨10,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨11,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨12,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨13,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨14,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨15,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨16,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨17,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨18,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨19,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨20,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨21,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨22,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨23,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨24,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨25,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨26,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨27,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨28,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨29,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨30,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨31,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨32,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨33,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨34,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨35,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨36,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨37,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨38,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨39,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨40,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨41,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨42,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨43,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨44,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨45,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨46,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨47,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨48,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨49,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨50,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨51,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12971) (by norm_num)
        (q := 1 - (cell12971 ⟨52,by decide⟩).lower)
        (by norm_num [cell12971]) (by norm_num [cell12971])
      exact ⟨E.1,E.2.trans (by norm_num [cell12971])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12971

/-! Source-cell containment and simple scalar guards at 12971. -/
namespace BstLean.Part269.N12971
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12971)
open BstLean.Part268 (cell12971)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12971 ⟨10,by decide⟩).lower ∧ (cell12971 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12971 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12971 ⟨11,by decide⟩).lower ∧ (cell12971 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12971 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12971 ⟨12,by decide⟩).lower ∧ (cell12971 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12971 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12971 ⟨13,by decide⟩).lower ∧ (cell12971 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12971 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12971 ⟨14,by decide⟩).lower ∧ (cell12971 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12971 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12971 ⟨15,by decide⟩).lower ∧ (cell12971 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12971 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12971 ⟨16,by decide⟩).lower ∧ (cell12971 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12971 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12971 ⟨17,by decide⟩).lower ∧ (cell12971 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12971 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12971 ⟨18,by decide⟩).lower ∧ (cell12971 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12971 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12971 ⟨19,by decide⟩).lower ∧ (cell12971 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12971 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12971 ⟨20,by decide⟩).lower ∧ (cell12971 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12971 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12971 ⟨21,by decide⟩).lower ∧ (cell12971 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12971 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12971 ⟨22,by decide⟩).lower ∧ (cell12971 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12971 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12971 ⟨23,by decide⟩).lower ∧ (cell12971 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12971 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12971 ⟨24,by decide⟩).lower ∧ (cell12971 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12971 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12971 ⟨25,by decide⟩).lower ∧ (cell12971 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12971 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12971 ⟨26,by decide⟩).lower ∧ (cell12971 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12971 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12971 ⟨27,by decide⟩).lower ∧ (cell12971 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12971 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12971 ⟨28,by decide⟩).lower ∧ (cell12971 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12971 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12971 ⟨29,by decide⟩).lower ∧ (cell12971 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12971 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12971 ⟨30,by decide⟩).lower ∧ (cell12971 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12971 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12971 ⟨31,by decide⟩).lower ∧ (cell12971 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12971 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12971 ⟨32,by decide⟩).lower ∧ (cell12971 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12971 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12971 ⟨33,by decide⟩).lower ∧ (cell12971 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12971 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12971 ⟨34,by decide⟩).lower ∧ (cell12971 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12971 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12971 ⟨35,by decide⟩).lower ∧ (cell12971 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12971 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12971 ⟨36,by decide⟩).lower ∧ (cell12971 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12971 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12971 ⟨37,by decide⟩).lower ∧ (cell12971 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12971 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12971 ⟨38,by decide⟩).lower ∧ (cell12971 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12971 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12971 ⟨39,by decide⟩).lower ∧ (cell12971 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12971 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12971 ⟨40,by decide⟩).lower ∧ (cell12971 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12971 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12971 ⟨41,by decide⟩).lower ∧ (cell12971 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12971 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12971 ⟨42,by decide⟩).lower ∧ (cell12971 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12971 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12971 ⟨43,by decide⟩).lower ∧ (cell12971 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12971 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12971 ⟨44,by decide⟩).lower ∧ (cell12971 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12971 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12971 ⟨45,by decide⟩).lower ∧ (cell12971 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12971 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12971 ⟨46,by decide⟩).lower ∧ (cell12971 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12971 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12971 ⟨47,by decide⟩).lower ∧ (cell12971 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12971 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12971 ⟨48,by decide⟩).lower ∧ (cell12971 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12971 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12971 ⟨49,by decide⟩).lower ∧ (cell12971 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12971 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12971 ⟨50,by decide⟩).lower ∧ (cell12971 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12971 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12971 ⟨51,by decide⟩).lower ∧ (cell12971 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12971 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12971 ⟨52,by decide⟩).lower ∧ (cell12971 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12971 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12971 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12971 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12971,cell12971,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12971 i).lower ∧
    (cell12971 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12971 i).upper ≤ (0.532 : ℝ) ∧
    (cell12971 i).centre ≤ (0.1 : ℝ) ∧ (cell12971 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12971 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12971 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12971

/-! The local source numeric instances at 12971 have no network premises. -/
namespace BstLean.Part269.N12971
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12971)
open BstLean.Part268 (cell12971)

noncomputable def sourceNumerics12971 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12971 (cell12971 i)
      scalarRow12971.M scalarRow12971.H scalarRow12971.xi := by
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
    energy_allowance := scalarRow12971.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12971]
    centre_nonneg := (scalarRow12971.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12971])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12971
/-! Actual 12972 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12972
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12972 ≤ (1.035428519334 : ℝ) := by
  have hr : (113.894688199230 : ℝ) ≤ √(12972 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.894688199230 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12972 12972 (11 / 1000) ≤
    (0.008392726361 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12972) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.894688199230 : ℝ) ≤ √(12972 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12972)
  have hdiv : K / √(12972 : ℝ) ≤ K / 113.894688199230 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.894688199230 ≤ (0.008392726361 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12972.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12972 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12972 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12972 := gPlus_lower 12972
end BstLean.Part269.N12972

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12972
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035428519333 : ℝ) ≤ wn 12972 := by
  have hn : √(12972 : ℝ) ≤ 113.894688199231 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12972 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.894688199231 ≤ 2 / √(12972 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246508735 : ℝ) ≤ rhoBar 12972 BstLean.Part154.csC ∧
    rhoBar 12972 BstLean.Part154.csC ≤ 0.000246509117 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035428519333 : ℝ) / (1.295212 * 12972) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035428519334 : ℝ) / (1.29521 * 12972) := by gcongr
      _ ≤ (0.000246509117 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12972 BstLean.Part154.csC) ≤ 0.000986097235 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12972 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12972 BstLean.Part154.csC) (piBar (rhoBar 12972 BstLean.Part154.csC)) ≤ 0.000188285140 ∧
    cc1 (rhoBar 12972 BstLean.Part154.csC) (piBar (rhoBar 12972 BstLean.Part154.csC)) ≤ 0.000119807123 ∧
    cc2 (rhoBar 12972 BstLean.Part154.csC) ≤ 0.000069549000 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12972 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12972 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12972 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12972 BstLean.Part154.csC * nuR (rhoBar 12972 BstLean.Part154.csC)) ≤ 0.000493033426 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246509117 : ℝ) * 0.000986097235 := by gcongr
      _ ≤ (0.000493033426 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12972 BstLean.Part154.csC) * nuR (rhoBar 12972 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000986097235 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12972 BstLean.Part154.csC) * rhoBar 12972 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246509117 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246509117 / 2 + 0.399 * 0.000986097235 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188285140 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000493033426 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119807123 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246509117 / 1.414213562 := by gcongr
      _ ≤ (0.000069549000 : ℝ) := by norm_num

end BstLean.Part269.N12972

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12972
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12972 BstLean.Part154.csC) (piBar (rhoBar 12972 BstLean.Part154.csC)) ≤ 1.53097E-7 := by
  have hr0 : 0 ≤ rhoBar 12972 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12972 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12972 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12972 BstLean.Part154.csC) (piBar (rhoBar 12972 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12972 BstLean.Part154.csC) (piBar (rhoBar 12972 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12972 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188285140 : ℝ) ^ 2 + 0.000119807123 ^ 2 + 3 * 0.000069549000 ^ 2 +
        2 * 0.797885 * 0.000188285140 * 0.000119807123 + 2 * 0.000188285140 * 0.000069549000 +
        4 * 0.797885 * 0.000119807123 * 0.000069549000 := by gcongr
    _ ≤ (1.53097E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12972 BstLean.Part154.csC Θ ≤ 0.002572257734 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12972 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12972 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12972 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12972 BstLean.Part154.csC) (piBar (rhoBar 12972 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12972 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035428519334 * 1.53097E-7 / (0.000246508735 : ℝ) := by gcongr
    _ ≤ 0.002572257734 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12972 BstLean.Part154.csC Θ ≤ 0.002853014625 + 0.000649970003 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12972 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12972 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12972 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035428519334 : ℝ) * ((2 * Θ * 0.000246509117 +
        (6863 / 10000) * 0.000246509117 * 12972 * 0.000986097235) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002853014625 + 0.000649970003 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12972 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12972 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12972 0.011 Θ ∧ gammaRatio 12972 0.011 Θ ≤ 0.000084743460 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12972 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035428519334 : ℝ) * 0.525 / ((1 - 0.011) * 12972) := by gcongr
      _ ≤ (0.000084743460 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12972 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12972 0.011 Θ) :=
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
    badAllowance 12972 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12972 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12972 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12972 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12972 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12972 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12972 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12972 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12972 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12972 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12972 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035428519334 : ℝ) * 12972 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12972 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003274371102 + 0.003222227737 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12972

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12972
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12972 BstLean.Part154.csC) (piBar (rhoBar 12972 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12972 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12972 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12972 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12972 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12972 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12972 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12972 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12972 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12972 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12972 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12972 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12972 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12972 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12972 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051925210862 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12972) ≤ 0.010485454590 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12972 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035428519334)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010485454590 + 2 * 0.737676 / 12972) := by gcongr
    _ ≤ (0.051925210862 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12972 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12972

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12972
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515611016 : ℝ) ≤ plow 12972 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12972) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052472640664)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350435311) : eMP 12972 0.011 xi bn ≤ 0.001162961565 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12972 : ℝ) * (1 - 0.011))) ≤ 0.000575056130 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001350435311 / (12972 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575056130 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575056130 : ℝ) + 3.141593 * 0.052472640664 / (12972 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001162961565 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052472640664)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350435311) : PiBarMP 12972 12 0.011 xi bn ≤ 0.159534570072 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12972 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036748269497 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.266535216717 : ℝ) ≤ √((12972 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.894688199230 : ℝ) ≤ √(12972 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12972) ≤ 0.122327111853 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036748269497 + 0.052472640664 * 1.772454 / (2 * (113.266535216717 : ℝ))) * (1 + 0.001162961565) +
        8 / (12972 * 113.894688199230) + 0.122327111853 := by gcongr
    _ ≤ (0.159534570072 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052472640664)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350435311) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280994284864) :
    parallelOracle 12972 0.011 xi bn cd ≤ 0.160504076447 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12972 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12972 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515611016 : ℝ) ≤ plow 12972 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.894688199230 : ℝ) ≤ √(12972 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280994284864 : ℝ) / (2 * 0.560515611016 * 113.894688199230)) * 0.159534570072 +
        0.280994284864 ^ 2 / (2 * 0.560515611016 * 113.894688199230) := by gcongr
    _ ≤ (0.160504076447 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052472640664) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350435311)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280994284864) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12972 12972 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515611016 : ℝ) ≤ plow 12972 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.894688199230 : ℝ) ≤ √(12972 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12972 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12972 Θ 1.22 ≤ 0.011643216387 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.894688199230 := by gcongr <;> linarith
      _ ≤ (0.011643216387 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12972 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12972 12972 0.011 ≤ 0.008392726361 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12972 12972 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12972 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12972 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12972 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12972 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160504076447 + 0.011643216387 + (0.008392726361 : ℝ) *
        (1 + 2 * (0.280994284864 + 0.011643216387) / (0.560515611016 * 113.894688199230))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12972]

end BstLean.Part269.N12972

/-! The original eight local profiles supply actual 12972 moment certificates. -/
namespace BstLean.Part269.N12972
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12972 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12972 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12972 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052472640664 ∧
    0 ≤ bN 12972 BstLean.Part154.csC (groupTheta g) ∧ bN 12972 BstLean.Part154.csC (groupTheta g) ≤ 0.001350435311 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12972 12972 0.011
      (momentAllowance 12972 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12972 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12972 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12972 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12972 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12972 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229069074002 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12972 0.011
      (momentAllowance 12972 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12972 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12972
/-! The actual computed-centre upper energy formula at 12972. -/
namespace BstLean.Part269.N12972
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12972

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12972
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12972)
open BstLean.Part268 (cell12972)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084733755374
  | 2 => 0.085663407751
  | 3 => 0.086589419157
  | 4 => 0.087512788975
  | 5 => 0.088434738390
  | 6 => 0.089356744873
  | 7 => 0.090280580207
  | 8 => 0.091208352140
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12972 12972 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12972 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12972

/-! Actual upper energy certificates on all 43 source endpoints at 12972. -/
namespace BstLean.Part269.N12972
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12972)
open BstLean.Part268 (cell12972)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12972 (gMinus 12972) (1 - (cell12972 i).lower) ≤ 1 ∧
    energyUpper 12972 (gMinus 12972) (BstLean.Part211.gPlus 12972)
      (finiteEnergy 12972 12972 0.011) (1 - (cell12972 i).lower) ≤
      (cell12972 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨10,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨11,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨12,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨13,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨14,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨15,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨16,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨17,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨18,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨19,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨20,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨21,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨22,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨23,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨24,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨25,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨26,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨27,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨28,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨29,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨30,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨31,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨32,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨33,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨34,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨35,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨36,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨37,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨38,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨39,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨40,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨41,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨42,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨43,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨44,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨45,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨46,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨47,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨48,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨49,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨50,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨51,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12972) (by norm_num)
        (q := 1 - (cell12972 ⟨52,by decide⟩).lower)
        (by norm_num [cell12972]) (by norm_num [cell12972])
      exact ⟨E.1,E.2.trans (by norm_num [cell12972])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12972

/-! Source-cell containment and simple scalar guards at 12972. -/
namespace BstLean.Part269.N12972
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12972)
open BstLean.Part268 (cell12972)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12972 ⟨10,by decide⟩).lower ∧ (cell12972 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12972 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12972 ⟨11,by decide⟩).lower ∧ (cell12972 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12972 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12972 ⟨12,by decide⟩).lower ∧ (cell12972 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12972 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12972 ⟨13,by decide⟩).lower ∧ (cell12972 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12972 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12972 ⟨14,by decide⟩).lower ∧ (cell12972 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12972 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12972 ⟨15,by decide⟩).lower ∧ (cell12972 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12972 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12972 ⟨16,by decide⟩).lower ∧ (cell12972 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12972 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12972 ⟨17,by decide⟩).lower ∧ (cell12972 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12972 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12972 ⟨18,by decide⟩).lower ∧ (cell12972 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12972 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12972 ⟨19,by decide⟩).lower ∧ (cell12972 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12972 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12972 ⟨20,by decide⟩).lower ∧ (cell12972 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12972 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12972 ⟨21,by decide⟩).lower ∧ (cell12972 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12972 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12972 ⟨22,by decide⟩).lower ∧ (cell12972 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12972 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12972 ⟨23,by decide⟩).lower ∧ (cell12972 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12972 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12972 ⟨24,by decide⟩).lower ∧ (cell12972 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12972 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12972 ⟨25,by decide⟩).lower ∧ (cell12972 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12972 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12972 ⟨26,by decide⟩).lower ∧ (cell12972 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12972 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12972 ⟨27,by decide⟩).lower ∧ (cell12972 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12972 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12972 ⟨28,by decide⟩).lower ∧ (cell12972 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12972 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12972 ⟨29,by decide⟩).lower ∧ (cell12972 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12972 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12972 ⟨30,by decide⟩).lower ∧ (cell12972 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12972 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12972 ⟨31,by decide⟩).lower ∧ (cell12972 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12972 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12972 ⟨32,by decide⟩).lower ∧ (cell12972 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12972 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12972 ⟨33,by decide⟩).lower ∧ (cell12972 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12972 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12972 ⟨34,by decide⟩).lower ∧ (cell12972 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12972 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12972 ⟨35,by decide⟩).lower ∧ (cell12972 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12972 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12972 ⟨36,by decide⟩).lower ∧ (cell12972 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12972 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12972 ⟨37,by decide⟩).lower ∧ (cell12972 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12972 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12972 ⟨38,by decide⟩).lower ∧ (cell12972 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12972 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12972 ⟨39,by decide⟩).lower ∧ (cell12972 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12972 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12972 ⟨40,by decide⟩).lower ∧ (cell12972 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12972 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12972 ⟨41,by decide⟩).lower ∧ (cell12972 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12972 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12972 ⟨42,by decide⟩).lower ∧ (cell12972 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12972 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12972 ⟨43,by decide⟩).lower ∧ (cell12972 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12972 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12972 ⟨44,by decide⟩).lower ∧ (cell12972 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12972 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12972 ⟨45,by decide⟩).lower ∧ (cell12972 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12972 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12972 ⟨46,by decide⟩).lower ∧ (cell12972 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12972 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12972 ⟨47,by decide⟩).lower ∧ (cell12972 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12972 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12972 ⟨48,by decide⟩).lower ∧ (cell12972 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12972 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12972 ⟨49,by decide⟩).lower ∧ (cell12972 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12972 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12972 ⟨50,by decide⟩).lower ∧ (cell12972 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12972 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12972 ⟨51,by decide⟩).lower ∧ (cell12972 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12972 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12972 ⟨52,by decide⟩).lower ∧ (cell12972 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12972 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12972 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12972 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12972,cell12972,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12972 i).lower ∧
    (cell12972 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12972 i).upper ≤ (0.532 : ℝ) ∧
    (cell12972 i).centre ≤ (0.1 : ℝ) ∧ (cell12972 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12972 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12972 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12972

/-! The local source numeric instances at 12972 have no network premises. -/
namespace BstLean.Part269.N12972
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12972)
open BstLean.Part268 (cell12972)

noncomputable def sourceNumerics12972 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12972 (cell12972 i)
      scalarRow12972.M scalarRow12972.H scalarRow12972.xi := by
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
    energy_allowance := scalarRow12972.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12972]
    centre_nonneg := (scalarRow12972.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12972])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12972
/-! Actual 12973 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12973
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12973 ≤ (1.035427141952 : ℝ) := by
  have hr : (113.899078134987 : ℝ) ≤ √(12973 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.899078134987 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12973 12973 (11 / 1000) ≤
    (0.008392402884 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12973) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.899078134987 : ℝ) ≤ √(12973 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12973)
  have hdiv : K / √(12973 : ℝ) ≤ K / 113.899078134987 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.899078134987 ≤ (0.008392402884 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12973.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12973 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12973 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12973 := gPlus_lower 12973
end BstLean.Part269.N12973

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12973
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035427141951 : ℝ) ≤ wn 12973 := by
  have hn : √(12973 : ℝ) ≤ 113.899078134988 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12973 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.899078134988 ≤ 2 / √(12973 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246489406 : ℝ) ≤ rhoBar 12973 BstLean.Part154.csC ∧
    rhoBar 12973 BstLean.Part154.csC ≤ 0.000246489787 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035427141951 : ℝ) / (1.295212 * 12973) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035427141952 : ℝ) / (1.29521 * 12973) := by gcongr
      _ ≤ (0.000246489787 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12973 BstLean.Part154.csC) ≤ 0.000986019906 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12973 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12973 BstLean.Part154.csC) (piBar (rhoBar 12973 BstLean.Part154.csC)) ≤ 0.000188270375 ∧
    cc1 (rhoBar 12973 BstLean.Part154.csC) (piBar (rhoBar 12973 BstLean.Part154.csC)) ≤ 0.000119797728 ∧
    cc2 (rhoBar 12973 BstLean.Part154.csC) ≤ 0.000069543546 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12973 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12973 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12973 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12973 BstLean.Part154.csC * nuR (rhoBar 12973 BstLean.Part154.csC)) ≤ 0.000492994764 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246489787 : ℝ) * 0.000986019906 := by gcongr
      _ ≤ (0.000492994764 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12973 BstLean.Part154.csC) * nuR (rhoBar 12973 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000986019906 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12973 BstLean.Part154.csC) * rhoBar 12973 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246489787 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246489787 / 2 + 0.399 * 0.000986019906 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188270375 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492994764 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119797728 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246489787 / 1.414213562 := by gcongr
      _ ≤ (0.000069543546 : ℝ) := by norm_num

end BstLean.Part269.N12973

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12973
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12973 BstLean.Part154.csC) (piBar (rhoBar 12973 BstLean.Part154.csC)) ≤ 1.53073E-7 := by
  have hr0 : 0 ≤ rhoBar 12973 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12973 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12973 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12973 BstLean.Part154.csC) (piBar (rhoBar 12973 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12973 BstLean.Part154.csC) (piBar (rhoBar 12973 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12973 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188270375 : ℝ) ^ 2 + 0.000119797728 ^ 2 + 3 * 0.000069543546 ^ 2 +
        2 * 0.797885 * 0.000188270375 * 0.000119797728 + 2 * 0.000188270375 * 0.000069543546 +
        4 * 0.797885 * 0.000119797728 * 0.000069543546 := by gcongr
    _ ≤ (1.53073E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12973 BstLean.Part154.csC Θ ≤ 0.002572052755 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12973 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12973 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12973 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12973 BstLean.Part154.csC) (piBar (rhoBar 12973 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12973 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035427141952 * 1.53073E-7 / (0.000246489406 : ℝ) := by gcongr
    _ ≤ 0.002572052755 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12973 BstLean.Part154.csC Θ ≤ 0.002852783299 + 0.000649918171 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12973 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12973 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12973 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035427141952 : ℝ) * ((2 * Θ * 0.000246489787 +
        (6863 / 10000) * 0.000246489787 * 12973 * 0.000986019906) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002852783299 + 0.000649918171 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12973 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12973 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12973 0.011 Θ ∧ gammaRatio 12973 0.011 Θ ≤ 0.000084736815 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12973 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035427141952 : ℝ) * 0.525 / ((1 - 0.011) * 12973) := by gcongr
      _ ≤ (0.000084736815 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12973 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12973 0.011 Θ) :=
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
    badAllowance 12973 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12973 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12973 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12973 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12973 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12973 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12973 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12973 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12973 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12973 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12973 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035427141952 : ℝ) * 12973 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12973 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003274139776 + 0.003221970926 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12973

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12973
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12973 BstLean.Part154.csC) (piBar (rhoBar 12973 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12973 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12973 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12973 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12973 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12973 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12973 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12973 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12973 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12973 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12973 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12973 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12973 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12973 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12973 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051923188068 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12973) ≤ 0.010485050456 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12973 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035427141952)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010485050456 + 2 * 0.737676 / 12973) := by gcongr
    _ ≤ (0.051923188068 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12973 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12973

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12973
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515654359 : ℝ) ≤ plow 12973 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12973) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052472274513)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350327697) : eMP 12973 0.011 xi bn ≤ 0.001162870333 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12973 : ℝ) * (1 - 0.011))) ≤ 0.000575011054 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001350327697 / (12973 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000575011054 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000575011054 : ℝ) + 3.141593 * 0.052472274513 / (12973 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001162870333 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052472274513)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350327697) : PiBarMP 12973 12 0.011 xi bn ≤ 0.159528366636 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12973 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036746805263 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.270900941062 : ℝ) ≤ √((12973 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.899078134987 : ℝ) ≤ √(12973 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12973) ≤ 0.122322397081 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036746805263 + 0.052472274513 * 1.772454 / (2 * (113.270900941062 : ℝ))) * (1 + 0.001162870333) +
        8 / (12973 * 113.899078134987) + 0.122322397081 := by gcongr
    _ ≤ (0.159528366636 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052472274513)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350327697) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280991462854) :
    parallelOracle 12973 0.011 xi bn cd ≤ 0.160497805970 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12973 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12973 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515654359 : ℝ) ≤ plow 12973 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.899078134987 : ℝ) ≤ √(12973 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280991462854 : ℝ) / (2 * 0.560515654359 * 113.899078134987)) * 0.159528366636 +
        0.280991462854 ^ 2 / (2 * 0.560515654359 * 113.899078134987) := by gcongr
    _ ≤ (0.160497805970 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052472274513) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350327697)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280991462854) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12973 12973 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515654359 : ℝ) ≤ plow 12973 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.899078134987 : ℝ) ≤ √(12973 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12973 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12973 Θ 1.22 ≤ 0.011642767631 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.899078134987 := by gcongr <;> linarith
      _ ≤ (0.011642767631 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12973 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12973 12973 0.011 ≤ 0.008392402884 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12973 12973 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12973 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12973 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12973 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12973 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160497805970 + 0.011642767631 + (0.008392402884 : ℝ) *
        (1 + 2 * (0.280991462854 + 0.011642767631) / (0.560515654359 * 113.899078134987))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12973]

end BstLean.Part269.N12973

/-! The original eight local profiles supply actual 12973 moment certificates. -/
namespace BstLean.Part269.N12973
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12973 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12973 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12973 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052472274513 ∧
    0 ≤ bN 12973 BstLean.Part154.csC (groupTheta g) ∧ bN 12973 BstLean.Part154.csC (groupTheta g) ≤ 0.001350327697 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12973 12973 0.011
      (momentAllowance 12973 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12973 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12973 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12973 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12973 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12973 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229068274786 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12973 0.011
      (momentAllowance 12973 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12973 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12973
/-! The actual computed-centre upper energy formula at 12973. -/
namespace BstLean.Part269.N12973
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12973

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12973
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12973)
open BstLean.Part268 (cell12973)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084731114266
  | 2 => 0.085660731282
  | 3 => 0.086586701875
  | 4 => 0.087510024158
  | 5 => 0.088431917812
  | 6 => 0.089353858547
  | 7 => 0.090277616090
  | 8 => 0.091205295808
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12973 12973 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12973 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12973

/-! Actual upper energy certificates on all 43 source endpoints at 12973. -/
namespace BstLean.Part269.N12973
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12973)
open BstLean.Part268 (cell12973)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12973 (gMinus 12973) (1 - (cell12973 i).lower) ≤ 1 ∧
    energyUpper 12973 (gMinus 12973) (BstLean.Part211.gPlus 12973)
      (finiteEnergy 12973 12973 0.011) (1 - (cell12973 i).lower) ≤
      (cell12973 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨10,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨11,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨12,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨13,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨14,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨15,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨16,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨17,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨18,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨19,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨20,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨21,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨22,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨23,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨24,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨25,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨26,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨27,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨28,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨29,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨30,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨31,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨32,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨33,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨34,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨35,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨36,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨37,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨38,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨39,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨40,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨41,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨42,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨43,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨44,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨45,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨46,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨47,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨48,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨49,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨50,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨51,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12973) (by norm_num)
        (q := 1 - (cell12973 ⟨52,by decide⟩).lower)
        (by norm_num [cell12973]) (by norm_num [cell12973])
      exact ⟨E.1,E.2.trans (by norm_num [cell12973])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12973

/-! Source-cell containment and simple scalar guards at 12973. -/
namespace BstLean.Part269.N12973
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12973)
open BstLean.Part268 (cell12973)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12973 ⟨10,by decide⟩).lower ∧ (cell12973 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12973 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12973 ⟨11,by decide⟩).lower ∧ (cell12973 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12973 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12973 ⟨12,by decide⟩).lower ∧ (cell12973 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12973 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12973 ⟨13,by decide⟩).lower ∧ (cell12973 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12973 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12973 ⟨14,by decide⟩).lower ∧ (cell12973 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12973 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12973 ⟨15,by decide⟩).lower ∧ (cell12973 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12973 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12973 ⟨16,by decide⟩).lower ∧ (cell12973 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12973 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12973 ⟨17,by decide⟩).lower ∧ (cell12973 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12973 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12973 ⟨18,by decide⟩).lower ∧ (cell12973 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12973 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12973 ⟨19,by decide⟩).lower ∧ (cell12973 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12973 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12973 ⟨20,by decide⟩).lower ∧ (cell12973 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12973 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12973 ⟨21,by decide⟩).lower ∧ (cell12973 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12973 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12973 ⟨22,by decide⟩).lower ∧ (cell12973 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12973 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12973 ⟨23,by decide⟩).lower ∧ (cell12973 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12973 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12973 ⟨24,by decide⟩).lower ∧ (cell12973 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12973 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12973 ⟨25,by decide⟩).lower ∧ (cell12973 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12973 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12973 ⟨26,by decide⟩).lower ∧ (cell12973 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12973 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12973 ⟨27,by decide⟩).lower ∧ (cell12973 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12973 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12973 ⟨28,by decide⟩).lower ∧ (cell12973 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12973 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12973 ⟨29,by decide⟩).lower ∧ (cell12973 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12973 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12973 ⟨30,by decide⟩).lower ∧ (cell12973 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12973 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12973 ⟨31,by decide⟩).lower ∧ (cell12973 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12973 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12973 ⟨32,by decide⟩).lower ∧ (cell12973 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12973 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12973 ⟨33,by decide⟩).lower ∧ (cell12973 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12973 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12973 ⟨34,by decide⟩).lower ∧ (cell12973 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12973 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12973 ⟨35,by decide⟩).lower ∧ (cell12973 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12973 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12973 ⟨36,by decide⟩).lower ∧ (cell12973 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12973 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12973 ⟨37,by decide⟩).lower ∧ (cell12973 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12973 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12973 ⟨38,by decide⟩).lower ∧ (cell12973 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12973 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12973 ⟨39,by decide⟩).lower ∧ (cell12973 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12973 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12973 ⟨40,by decide⟩).lower ∧ (cell12973 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12973 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12973 ⟨41,by decide⟩).lower ∧ (cell12973 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12973 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12973 ⟨42,by decide⟩).lower ∧ (cell12973 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12973 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12973 ⟨43,by decide⟩).lower ∧ (cell12973 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12973 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12973 ⟨44,by decide⟩).lower ∧ (cell12973 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12973 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12973 ⟨45,by decide⟩).lower ∧ (cell12973 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12973 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12973 ⟨46,by decide⟩).lower ∧ (cell12973 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12973 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12973 ⟨47,by decide⟩).lower ∧ (cell12973 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12973 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12973 ⟨48,by decide⟩).lower ∧ (cell12973 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12973 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12973 ⟨49,by decide⟩).lower ∧ (cell12973 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12973 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12973 ⟨50,by decide⟩).lower ∧ (cell12973 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12973 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12973 ⟨51,by decide⟩).lower ∧ (cell12973 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12973 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12973 ⟨52,by decide⟩).lower ∧ (cell12973 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12973 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12973 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12973 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12973,cell12973,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12973 i).lower ∧
    (cell12973 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12973 i).upper ≤ (0.532 : ℝ) ∧
    (cell12973 i).centre ≤ (0.1 : ℝ) ∧ (cell12973 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12973 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12973 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12973

/-! The local source numeric instances at 12973 have no network premises. -/
namespace BstLean.Part269.N12973
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12973)
open BstLean.Part268 (cell12973)

noncomputable def sourceNumerics12973 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12973 (cell12973 i)
      scalarRow12973.M scalarRow12973.H scalarRow12973.xi := by
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
    energy_allowance := scalarRow12973.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12973]
    centre_nonneg := (scalarRow12973.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12973])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12973
/-! Actual 12974 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12974
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12974 ≤ (1.035425764730 : ℝ) := by
  have hr : (113.903467901552 : ℝ) ≤ √(12974 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.903467901552 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12974 12974 (11 / 1000) ≤
    (0.008392079443 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12974) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.903467901552 : ℝ) ≤ √(12974 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12974)
  have hdiv : K / √(12974 : ℝ) ≤ K / 113.903467901552 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.903467901552 ≤ (0.008392079443 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12974.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12974 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12974 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12974 := gPlus_lower 12974
end BstLean.Part269.N12974

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12974
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035425764729 : ℝ) ≤ wn 12974 := by
  have hn : √(12974 : ℝ) ≤ 113.903467901553 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12974 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.903467901553 ≤ 2 / √(12974 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000246470079 : ℝ) ≤ rhoBar 12974 BstLean.Part154.csC ∧
    rhoBar 12974 BstLean.Part154.csC ≤ 0.000246470461 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035425764729 : ℝ) / (1.295212 * 12974) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035425764730 : ℝ) / (1.29521 * 12974) := by gcongr
      _ ≤ (0.000246470461 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12974 BstLean.Part154.csC) ≤ 0.000985942592 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12974 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12974 BstLean.Part154.csC) (piBar (rhoBar 12974 BstLean.Part154.csC)) ≤ 0.000188255613 ∧
    cc1 (rhoBar 12974 BstLean.Part154.csC) (piBar (rhoBar 12974 BstLean.Part154.csC)) ≤ 0.000119788335 ∧
    cc2 (rhoBar 12974 BstLean.Part154.csC) ≤ 0.000069538093 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12974 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12974 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12974 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12974 BstLean.Part154.csC * nuR (rhoBar 12974 BstLean.Part154.csC)) ≤ 0.000492956109 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000246470461 : ℝ) * 0.000985942592 := by gcongr
      _ ≤ (0.000492956109 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12974 BstLean.Part154.csC) * nuR (rhoBar 12974 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000985942592 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12974 BstLean.Part154.csC) * rhoBar 12974 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000246470461 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000246470461 / 2 + 0.399 * 0.000985942592 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188255613 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000492956109 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000119788335 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000246470461 / 1.414213562 := by gcongr
      _ ≤ (0.000069538093 : ℝ) := by norm_num

end BstLean.Part269.N12974

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12974
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12974 BstLean.Part154.csC) (piBar (rhoBar 12974 BstLean.Part154.csC)) ≤ 1.53049E-7 := by
  have hr0 : 0 ≤ rhoBar 12974 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12974 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12974 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12974 BstLean.Part154.csC) (piBar (rhoBar 12974 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12974 BstLean.Part154.csC) (piBar (rhoBar 12974 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12974 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188255613 : ℝ) ^ 2 + 0.000119788335 ^ 2 + 3 * 0.000069538093 ^ 2 +
        2 * 0.797885 * 0.000188255613 * 0.000119788335 + 2 * 0.000188255613 * 0.000069538093 +
        4 * 0.797885 * 0.000119788335 * 0.000069538093 := by gcongr
    _ ≤ (1.53049E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12974 BstLean.Part154.csC Θ ≤ 0.002571847724 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12974 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12974 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12974 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12974 BstLean.Part154.csC) (piBar (rhoBar 12974 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12974 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035425764730 * 1.53049E-7 / (0.000246470079 : ℝ) := by gcongr
    _ ≤ 0.002571847724 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12974 BstLean.Part154.csC Θ ≤ 0.002852552030 + 0.000649866350 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12974 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12974 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12974 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035425764730 : ℝ) * ((2 * Θ * 0.000246470461 +
        (6863 / 10000) * 0.000246470461 * 12974 * 0.000985942592) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002852552030 + 0.000649866350 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12974 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12974 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12974 0.011 Θ ∧ gammaRatio 12974 0.011 Θ ≤ 0.000084730171 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12974 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035425764730 : ℝ) * 0.525 / ((1 - 0.011) * 12974) := by gcongr
      _ ≤ (0.000084730171 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12974 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12974 0.011 Θ) :=
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
    badAllowance 12974 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000421356477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12974 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12974 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12974 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12974 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12974 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12974 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12974 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12974 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12974 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12974 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035425764730 : ℝ) * 12974 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000421356477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12974 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003273908507 + 0.003221714074 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12974

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12974
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12974 BstLean.Part154.csC) (piBar (rhoBar 12974 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12974 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12974 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12974 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12974 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12974 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12974 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12974 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12974 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12974 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12974 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12974 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12974 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12974 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12974 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051921165512 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12974) ≤ 0.010484646369 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12974 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035425764730)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010484646369 + 2 * 0.737676 / 12974) := by gcongr
    _ ≤ (0.051921165512 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12974 12 ≤ 0.0015 := by
  exact BstLean.Part269.S24.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12974

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12974
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560515697695 : ℝ) ≤ plow 12974 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12974) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052471908396)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350220056) : eMP 12974 0.011 xi bn ≤ 0.001162779095 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12974 : ℝ) * (1 - 0.011))) ≤ 0.000574965975 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001350220056 / (12974 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000574965975 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000574965975 : ℝ) + 3.141593 * 0.052471908396 / (12974 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001162779095 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052471908396)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350220056) : PiBarMP 12974 12 0.011 xi bn ≤ 0.159522163322 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12974 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036745340603 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.275266497148 : ℝ) ≤ √((12974 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.903467901552 : ℝ) ≤ √(12974 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12974) ≤ 0.122317682854 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036745340603 + 0.052471908396 * 1.772454 / (2 * (113.275266497148 : ℝ))) * (1 + 0.001162779095) +
        8 / (12974 * 113.903467901552) + 0.122317682854 := by gcongr
    _ ≤ (0.159522163322 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052471908396)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350220056) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280988641152) :
    parallelOracle 12974 0.011 xi bn cd ≤ 0.160491535625 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12974 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12974 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560515697695 : ℝ) ≤ plow 12974 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.903467901552 : ℝ) ≤ √(12974 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280988641152 : ℝ) / (2 * 0.560515697695 * 113.903467901552)) * 0.159522163322 +
        0.280988641152 ^ 2 / (2 * 0.560515697695 * 113.903467901552) := by gcongr
    _ ≤ (0.160491535625 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052471908396) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001350220056)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280988641152) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12974 12974 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560515697695 : ℝ) ≤ plow 12974 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.903467901552 : ℝ) ≤ √(12974 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12974 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12974 Θ 1.22 ≤ 0.011642318926 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.903467901552 := by gcongr <;> linarith
      _ ≤ (0.011642318926 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12974 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12974 12974 0.011 ≤ 0.008392079443 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12974 12974 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12974 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12974 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12974 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12974 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160491535625 + 0.011642318926 + (0.008392079443 : ℝ) *
        (1 + 2 * (0.280988641152 + 0.011642318926) / (0.560515697695 * 113.903467901552))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12974]

end BstLean.Part269.N12974

/-! The original eight local profiles supply actual 12974 moment certificates. -/
namespace BstLean.Part269.N12974
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12974 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12974 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12974 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052471908396 ∧
    0 ≤ bN 12974 BstLean.Part154.csC (groupTheta g) ∧ bN 12974 BstLean.Part154.csC (groupTheta g) ≤ 0.001350220056 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12974 12974 0.011
      (momentAllowance 12974 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12974 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12974 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12974 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12974 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12974 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229067475640 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12974 0.011
      (momentAllowance 12974 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12974 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12974
/-! The actual computed-centre upper energy formula at 12974. -/
namespace BstLean.Part269.N12974
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12974

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12974
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12974)
open BstLean.Part268 (cell12974)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084728473986
  | 2 => 0.085658055671
  | 3 => 0.086583985488
  | 4 => 0.087507260280
  | 5 => 0.088429098229
  | 6 => 0.089350973285
  | 7 => 0.090274653119
  | 8 => 0.091202240720
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12974 12974 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12974 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003279469477 + 0.003227897328 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S24.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S24.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12974

/-! Actual upper energy certificates on all 43 source endpoints at 12974. -/
namespace BstLean.Part269.N12974
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12974)
open BstLean.Part268 (cell12974)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12974 (gMinus 12974) (1 - (cell12974 i).lower) ≤ 1 ∧
    energyUpper 12974 (gMinus 12974) (BstLean.Part211.gPlus 12974)
      (finiteEnergy 12974 12974 0.011) (1 - (cell12974 i).lower) ≤
      (cell12974 i).energy := by
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
      have E := BstLean.Part269.S24.uniformEnergy10 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨10,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy11 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨11,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy12 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨12,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy13 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨13,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy14 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨14,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy15 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨15,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy16 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨16,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy17 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨17,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy18 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨18,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy19 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨19,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy20 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨20,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy21 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨21,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy22 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨22,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy23 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨23,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy24 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨24,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy25 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨25,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy26 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨26,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy27 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨27,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy28 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨28,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy29 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨29,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy30 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨30,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy31 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨31,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy32 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨32,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy33 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨33,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy34 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨34,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy35 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨35,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy36 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨36,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy37 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨37,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy38 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨38,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy39 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨39,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy40 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨40,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy41 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨41,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy42 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨42,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy43 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨43,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy44 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨44,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy45 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨45,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy46 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨46,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy47 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨47,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy48 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨48,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy49 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨49,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy50 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨50,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy51 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨51,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S24.uniformEnergy52 (n := 12974) (by norm_num)
        (q := 1 - (cell12974 ⟨52,by decide⟩).lower)
        (by norm_num [cell12974]) (by norm_num [cell12974])
      exact ⟨E.1,E.2.trans (by norm_num [cell12974])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12974

/-! Source-cell containment and simple scalar guards at 12974. -/
namespace BstLean.Part269.N12974
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12974)
open BstLean.Part268 (cell12974)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12974 ⟨10,by decide⟩).lower ∧ (cell12974 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12974 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12974 ⟨11,by decide⟩).lower ∧ (cell12974 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12974 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12974 ⟨12,by decide⟩).lower ∧ (cell12974 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12974 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12974 ⟨13,by decide⟩).lower ∧ (cell12974 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12974 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12974 ⟨14,by decide⟩).lower ∧ (cell12974 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12974 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12974 ⟨15,by decide⟩).lower ∧ (cell12974 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12974 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12974 ⟨16,by decide⟩).lower ∧ (cell12974 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12974 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12974 ⟨17,by decide⟩).lower ∧ (cell12974 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12974 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12974 ⟨18,by decide⟩).lower ∧ (cell12974 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12974 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12974 ⟨19,by decide⟩).lower ∧ (cell12974 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12974 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12974 ⟨20,by decide⟩).lower ∧ (cell12974 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12974 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12974 ⟨21,by decide⟩).lower ∧ (cell12974 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12974 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12974 ⟨22,by decide⟩).lower ∧ (cell12974 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12974 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12974 ⟨23,by decide⟩).lower ∧ (cell12974 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12974 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12974 ⟨24,by decide⟩).lower ∧ (cell12974 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12974 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12974 ⟨25,by decide⟩).lower ∧ (cell12974 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12974 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12974 ⟨26,by decide⟩).lower ∧ (cell12974 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12974 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12974 ⟨27,by decide⟩).lower ∧ (cell12974 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12974 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12974 ⟨28,by decide⟩).lower ∧ (cell12974 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12974 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12974 ⟨29,by decide⟩).lower ∧ (cell12974 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12974 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12974 ⟨30,by decide⟩).lower ∧ (cell12974 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12974 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12974 ⟨31,by decide⟩).lower ∧ (cell12974 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12974 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12974 ⟨32,by decide⟩).lower ∧ (cell12974 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12974 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12974 ⟨33,by decide⟩).lower ∧ (cell12974 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12974 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12974 ⟨34,by decide⟩).lower ∧ (cell12974 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12974 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12974 ⟨35,by decide⟩).lower ∧ (cell12974 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12974 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12974 ⟨36,by decide⟩).lower ∧ (cell12974 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12974 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12974 ⟨37,by decide⟩).lower ∧ (cell12974 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12974 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12974 ⟨38,by decide⟩).lower ∧ (cell12974 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12974 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12974 ⟨39,by decide⟩).lower ∧ (cell12974 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12974 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12974 ⟨40,by decide⟩).lower ∧ (cell12974 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12974 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12974 ⟨41,by decide⟩).lower ∧ (cell12974 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12974 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12974 ⟨42,by decide⟩).lower ∧ (cell12974 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12974 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12974 ⟨43,by decide⟩).lower ∧ (cell12974 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12974 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12974 ⟨44,by decide⟩).lower ∧ (cell12974 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12974 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12974 ⟨45,by decide⟩).lower ∧ (cell12974 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12974 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12974 ⟨46,by decide⟩).lower ∧ (cell12974 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12974 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12974 ⟨47,by decide⟩).lower ∧ (cell12974 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12974 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12974 ⟨48,by decide⟩).lower ∧ (cell12974 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12974 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12974 ⟨49,by decide⟩).lower ∧ (cell12974 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12974 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12974 ⟨50,by decide⟩).lower ∧ (cell12974 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12974 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12974 ⟨51,by decide⟩).lower ∧ (cell12974 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12974 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12974 ⟨52,by decide⟩).lower ∧ (cell12974 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12974 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12974 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12974 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12974,cell12974,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12974 i).lower ∧
    (cell12974 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12974 i).upper ≤ (0.532 : ℝ) ∧
    (cell12974 i).centre ≤ (0.1 : ℝ) ∧ (cell12974 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12974 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12974 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12974

/-! The local source numeric instances at 12974 have no network premises. -/
namespace BstLean.Part269.N12974
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12974)
open BstLean.Part268 (cell12974)

noncomputable def sourceNumerics12974 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12974 (cell12974 i)
      scalarRow12974.M scalarRow12974.H scalarRow12974.xi := by
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
    energy_allowance := scalarRow12974.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12974]
    centre_nonneg := (scalarRow12974.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D24.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12974])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12974