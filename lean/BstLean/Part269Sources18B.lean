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
import BstLean.Part269Direction18
import BstLean.Part269Shared18
import BstLean.Part269Finite
import BstLean.Part269Rows18
import BstLean.Part269Source
/-! Actual 12813 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12813
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12813 ≤ (1.035649581780 : ℝ) := by
  have hr : (113.194522835692 : ℝ) ≤ √(12813 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.194522835692 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12813 12813 (11 / 1000) ≤
    (0.008444640012 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12813) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.194522835692 : ℝ) ≤ √(12813 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12813)
  have hdiv : K / √(12813 : ℝ) ≤ K / 113.194522835692 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.194522835692 ≤ (0.008444640012 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12813.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12813 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12813 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12813 := gPlus_lower 12813
end BstLean.Part269.N12813

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12813
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035649581779 : ℝ) ≤ wn 12813 := by
  have hn : √(12813 : ℝ) ≤ 113.194522835693 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12813 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.194522835693 ≤ 2 / √(12813 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249621012 : ℝ) ≤ rhoBar 12813 BstLean.Part154.csC ∧
    rhoBar 12813 BstLean.Part154.csC ≤ 0.000249621398 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035649581779 : ℝ) / (1.295212 * 12813) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035649581780 : ℝ) / (1.29521 * 12813) := by gcongr
      _ ≤ (0.000249621398 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12813 BstLean.Part154.csC) ≤ 0.000998547903 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12813 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12813 BstLean.Part154.csC) (piBar (rhoBar 12813 BstLean.Part154.csC)) ≤ 0.000190662428 ∧
    cc1 (rhoBar 12813 BstLean.Part154.csC) (piBar (rhoBar 12813 BstLean.Part154.csC)) ≤ 0.000121319785 ∧
    cc2 (rhoBar 12813 BstLean.Part154.csC) ≤ 0.000070427085 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12813 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12813 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12813 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12813 BstLean.Part154.csC * nuR (rhoBar 12813 BstLean.Part154.csC)) ≤ 0.000499258374 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249621398 : ℝ) * 0.000998547903 := by gcongr
      _ ≤ (0.000499258374 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12813 BstLean.Part154.csC) * nuR (rhoBar 12813 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000998547903 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12813 BstLean.Part154.csC) * rhoBar 12813 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249621398 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249621398 / 2 + 0.399 * 0.000998547903 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190662428 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499258374 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121319785 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249621398 / 1.414213562 := by gcongr
      _ ≤ (0.000070427085 : ℝ) := by norm_num

end BstLean.Part269.N12813

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12813
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12813 BstLean.Part154.csC) (piBar (rhoBar 12813 BstLean.Part154.csC)) ≤ 1.56988E-7 := by
  have hr0 : 0 ≤ rhoBar 12813 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12813 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12813 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12813 BstLean.Part154.csC) (piBar (rhoBar 12813 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12813 BstLean.Part154.csC) (piBar (rhoBar 12813 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12813 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190662428 : ℝ) ^ 2 + 0.000121319785 ^ 2 + 3 * 0.000070427085 ^ 2 +
        2 * 0.797885 * 0.000190662428 * 0.000121319785 + 2 * 0.000190662428 * 0.000070427085 +
        4 * 0.797885 * 0.000121319785 * 0.000070427085 := by gcongr
    _ ≤ (1.56988E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12813 BstLean.Part154.csC Θ ≤ 0.002605302419 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12813 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12813 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12813 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12813 BstLean.Part154.csC) (piBar (rhoBar 12813 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12813 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035649581780 * 1.56988E-7 / (0.000249621012 : ℝ) := by gcongr
    _ ≤ 0.002605302419 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12813 BstLean.Part154.csC Θ ≤ 0.002890271120 + 0.000658316667 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12813 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12813 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12813 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035649581780 : ℝ) * ((2 * Θ * 0.000249621398 +
        (6863 / 10000) * 0.000249621398 * 12813 * 0.000998547903) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002890271120 + 0.000658316667 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12813 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12813 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12813 0.011 Θ ∧ gammaRatio 12813 0.011 Θ ≤ 0.000085813382 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12813 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035649581780 : ℝ) * 0.525 / ((1 - 0.011) * 12813) := by gcongr
      _ ≤ (0.000085813382 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12813 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12813 0.011 Θ) :=
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
    badAllowance 12813 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12813 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12813 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12813 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12813 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12813 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12813 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12813 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12813 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12813 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12813 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035649581780 : ℝ) * 12813 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12813 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003399075620 + 0.003263619086 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12813

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12813
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12813 BstLean.Part154.csC) (piBar (rhoBar 12813 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12813 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12813 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12813 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12813 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12813 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12813 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12813 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12813 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12813 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12813 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12813 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12813 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12813 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12813 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052249862293 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12813) ≤ 0.010550312428 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12813 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035649581780)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010550312428 + 2 * 0.737676 / 12813) := by gcongr
    _ ≤ (0.052249862293 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12813 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12813

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12813
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508633419 : ℝ) ≤ plow 12813 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12813) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052619075641)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367783770) : eMP 12813 0.011 xi bn ≤ 0.001177680817 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12813 : ℝ) * (1 - 0.011))) ≤ 0.000582317879 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001367783770 / (12813 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582317879 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582317879 : ℝ) + 3.141593 * 0.052619075641 / (12813 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001177680817 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052619075641)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367783770) : PiBarMP 12813 12 0.011 xi bn ≤ 0.160531138278 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12813 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036983560808 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.570231411328 : ℝ) ≤ √((12813 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.194522835692 : ℝ) ≤ √(12813 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12813) ≤ 0.123083766898 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036983560808 + 0.052619075641 * 1.772454 / (2 * (112.570231411328 : ℝ))) * (1 + 0.001177680817) +
        8 / (12813 * 113.194522835692) + 0.123083766898 := by gcongr
    _ ≤ (0.160531138278 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052619075641)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367783770) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281638344221) :
    parallelOracle 12813 0.011 xi bn cd ≤ 0.161512531000 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12813 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12813 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508633419 : ℝ) ≤ plow 12813 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.194522835692 : ℝ) ≤ √(12813 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281638344221 : ℝ) / (2 * 0.560508633419 * 113.194522835692)) * 0.160531138278 +
        0.281638344221 ^ 2 / (2 * 0.560508633419 * 113.194522835692) := by gcongr
    _ ≤ (0.161512531000 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052619075641) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367783770)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281638344221) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12813 12813 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508633419 : ℝ) ≤ plow 12813 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.194522835692 : ℝ) ≤ √(12813 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12813 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12813 Θ 1.22 ≤ 0.011715235568 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.194522835692 := by gcongr <;> linarith
      _ ≤ (0.011715235568 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12813 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12813 12813 0.011 ≤ 0.008444640012 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12813 12813 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12813 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12813 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12813 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12813 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161512531000 + 0.011715235568 + (0.008444640012 : ℝ) *
        (1 + 2 * (0.281638344221 + 0.011715235568) / (0.560508633419 * 113.194522835692))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12813]

end BstLean.Part269.N12813

/-! The original eight local profiles supply actual 12813 moment certificates. -/
namespace BstLean.Part269.N12813
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12813 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12813 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12813 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052619075641 ∧
    0 ≤ bN 12813 BstLean.Part154.csC (groupTheta g) ∧ bN 12813 BstLean.Part154.csC (groupTheta g) ≤ 0.001367783770 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12813 12813 0.011
      (momentAllowance 12813 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12813 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12813 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12813 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12813 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12813 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229388481928 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12813 0.011
      (momentAllowance 12813 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12813 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12813
/-! The actual computed-centre upper energy formula at 12813. -/
namespace BstLean.Part269.N12813
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12813

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12813
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12813)
open BstLean.Part268 (cell12813)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085167380669
  | 2 => 0.086104346238
  | 3 => 0.087038631854
  | 4 => 0.087971465115
  | 5 => 0.088904336875
  | 6 => 0.089839041111
  | 7 => 0.090777718688
  | 8 => 0.091722905082
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12813 12813 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12813 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12813

/-! Actual upper energy certificates on all 43 source endpoints at 12813. -/
namespace BstLean.Part269.N12813
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12813)
open BstLean.Part268 (cell12813)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12813 (gMinus 12813) (1 - (cell12813 i).lower) ≤ 1 ∧
    energyUpper 12813 (gMinus 12813) (BstLean.Part211.gPlus 12813)
      (finiteEnergy 12813 12813 0.011) (1 - (cell12813 i).lower) ≤
      (cell12813 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨10,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨11,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨12,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨13,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨14,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨15,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨16,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨17,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨18,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨19,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨20,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨21,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨22,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨23,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨24,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨25,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨26,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨27,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨28,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨29,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨30,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨31,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨32,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨33,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨34,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨35,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨36,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨37,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨38,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨39,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨40,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨41,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨42,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨43,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨44,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨45,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨46,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨47,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨48,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨49,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨50,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨51,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12813) (by norm_num)
        (q := 1 - (cell12813 ⟨52,by decide⟩).lower)
        (by norm_num [cell12813]) (by norm_num [cell12813])
      exact ⟨E.1,E.2.trans (by norm_num [cell12813])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12813

/-! Source-cell containment and simple scalar guards at 12813. -/
namespace BstLean.Part269.N12813
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12813)
open BstLean.Part268 (cell12813)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12813 ⟨10,by decide⟩).lower ∧ (cell12813 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12813 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12813 ⟨11,by decide⟩).lower ∧ (cell12813 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12813 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12813 ⟨12,by decide⟩).lower ∧ (cell12813 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12813 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12813 ⟨13,by decide⟩).lower ∧ (cell12813 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12813 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12813 ⟨14,by decide⟩).lower ∧ (cell12813 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12813 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12813 ⟨15,by decide⟩).lower ∧ (cell12813 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12813 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12813 ⟨16,by decide⟩).lower ∧ (cell12813 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12813 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12813 ⟨17,by decide⟩).lower ∧ (cell12813 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12813 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12813 ⟨18,by decide⟩).lower ∧ (cell12813 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12813 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12813 ⟨19,by decide⟩).lower ∧ (cell12813 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12813 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12813 ⟨20,by decide⟩).lower ∧ (cell12813 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12813 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12813 ⟨21,by decide⟩).lower ∧ (cell12813 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12813 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12813 ⟨22,by decide⟩).lower ∧ (cell12813 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12813 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12813 ⟨23,by decide⟩).lower ∧ (cell12813 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12813 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12813 ⟨24,by decide⟩).lower ∧ (cell12813 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12813 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12813 ⟨25,by decide⟩).lower ∧ (cell12813 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12813 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12813 ⟨26,by decide⟩).lower ∧ (cell12813 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12813 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12813 ⟨27,by decide⟩).lower ∧ (cell12813 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12813 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12813 ⟨28,by decide⟩).lower ∧ (cell12813 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12813 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12813 ⟨29,by decide⟩).lower ∧ (cell12813 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12813 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12813 ⟨30,by decide⟩).lower ∧ (cell12813 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12813 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12813 ⟨31,by decide⟩).lower ∧ (cell12813 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12813 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12813 ⟨32,by decide⟩).lower ∧ (cell12813 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12813 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12813 ⟨33,by decide⟩).lower ∧ (cell12813 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12813 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12813 ⟨34,by decide⟩).lower ∧ (cell12813 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12813 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12813 ⟨35,by decide⟩).lower ∧ (cell12813 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12813 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12813 ⟨36,by decide⟩).lower ∧ (cell12813 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12813 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12813 ⟨37,by decide⟩).lower ∧ (cell12813 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12813 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12813 ⟨38,by decide⟩).lower ∧ (cell12813 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12813 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12813 ⟨39,by decide⟩).lower ∧ (cell12813 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12813 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12813 ⟨40,by decide⟩).lower ∧ (cell12813 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12813 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12813 ⟨41,by decide⟩).lower ∧ (cell12813 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12813 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12813 ⟨42,by decide⟩).lower ∧ (cell12813 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12813 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12813 ⟨43,by decide⟩).lower ∧ (cell12813 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12813 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12813 ⟨44,by decide⟩).lower ∧ (cell12813 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12813 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12813 ⟨45,by decide⟩).lower ∧ (cell12813 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12813 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12813 ⟨46,by decide⟩).lower ∧ (cell12813 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12813 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12813 ⟨47,by decide⟩).lower ∧ (cell12813 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12813 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12813 ⟨48,by decide⟩).lower ∧ (cell12813 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12813 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12813 ⟨49,by decide⟩).lower ∧ (cell12813 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12813 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12813 ⟨50,by decide⟩).lower ∧ (cell12813 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12813 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12813 ⟨51,by decide⟩).lower ∧ (cell12813 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12813 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12813 ⟨52,by decide⟩).lower ∧ (cell12813 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12813 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12813 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12813 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12813,cell12813,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12813 i).lower ∧
    (cell12813 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12813 i).upper ≤ (0.532 : ℝ) ∧
    (cell12813 i).centre ≤ (0.1 : ℝ) ∧ (cell12813 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12813 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12813 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12813

/-! The local source numeric instances at 12813 have no network premises. -/
namespace BstLean.Part269.N12813
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12813)
open BstLean.Part268 (cell12813)

noncomputable def sourceNumerics12813 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12813 (cell12813 i)
      scalarRow12813.M scalarRow12813.H scalarRow12813.xi := by
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
    energy_allowance := scalarRow12813.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12813]
    centre_nonneg := (scalarRow12813.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12813])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12813
/-! Actual 12814 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12814
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12814 ≤ (1.035648178532 : ℝ) := by
  have hr : (113.198939924365 : ℝ) ≤ √(12814 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.198939924365 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12814 12814 (11 / 1000) ≤
    (0.008444310495 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12814) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.198939924365 : ℝ) ≤ √(12814 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12814)
  have hdiv : K / √(12814 : ℝ) ≤ K / 113.198939924365 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.198939924365 ≤ (0.008444310495 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12814.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12814 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12814 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12814 := gPlus_lower 12814
end BstLean.Part269.N12814

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12814
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035648178531 : ℝ) ≤ wn 12814 := by
  have hn : √(12814 : ℝ) ≤ 113.198939924366 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12814 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.198939924366 ≤ 2 / √(12814 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249601193 : ℝ) ≤ rhoBar 12814 BstLean.Part154.csC ∧
    rhoBar 12814 BstLean.Part154.csC ≤ 0.000249601580 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035648178531 : ℝ) / (1.295212 * 12814) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035648178532 : ℝ) / (1.29521 * 12814) := by gcongr
      _ ≤ (0.000249601580 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12814 BstLean.Part154.csC) ≤ 0.000998468621 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12814 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12814 BstLean.Part154.csC) (piBar (rhoBar 12814 BstLean.Part154.csC)) ≤ 0.000190647290 ∧
    cc1 (rhoBar 12814 BstLean.Part154.csC) (piBar (rhoBar 12814 BstLean.Part154.csC)) ≤ 0.000121310153 ∧
    cc2 (rhoBar 12814 BstLean.Part154.csC) ≤ 0.000070421493 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12814 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12814 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12814 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12814 BstLean.Part154.csC * nuR (rhoBar 12814 BstLean.Part154.csC)) ≤ 0.000499218736 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249601580 : ℝ) * 0.000998468621 := by gcongr
      _ ≤ (0.000499218736 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12814 BstLean.Part154.csC) * nuR (rhoBar 12814 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000998468621 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12814 BstLean.Part154.csC) * rhoBar 12814 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249601580 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249601580 / 2 + 0.399 * 0.000998468621 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190647290 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499218736 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121310153 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249601580 / 1.414213562 := by gcongr
      _ ≤ (0.000070421493 : ℝ) := by norm_num

end BstLean.Part269.N12814

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12814
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12814 BstLean.Part154.csC) (piBar (rhoBar 12814 BstLean.Part154.csC)) ≤ 1.56963E-7 := by
  have hr0 : 0 ≤ rhoBar 12814 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12814 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12814 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12814 BstLean.Part154.csC) (piBar (rhoBar 12814 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12814 BstLean.Part154.csC) (piBar (rhoBar 12814 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12814 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190647290 : ℝ) ^ 2 + 0.000121310153 ^ 2 + 3 * 0.000070421493 ^ 2 +
        2 * 0.797885 * 0.000190647290 * 0.000121310153 + 2 * 0.000190647290 * 0.000070421493 +
        4 * 0.797885 * 0.000121310153 * 0.000070421493 := by gcongr
    _ ≤ (1.56963E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12814 BstLean.Part154.csC Θ ≤ 0.002605090835 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12814 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12814 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12814 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12814 BstLean.Part154.csC) (piBar (rhoBar 12814 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12814 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035648178532 * 1.56963E-7 / (0.000249601193 : ℝ) := by gcongr
    _ ≤ 0.002605090835 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12814 BstLean.Part154.csC Θ ≤ 0.002890033815 + 0.000658263509 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12814 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12814 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12814 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035648178532 : ℝ) * ((2 * Θ * 0.000249601580 +
        (6863 / 10000) * 0.000249601580 * 12814 * 0.000998468621) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002890033815 + 0.000658263509 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12814 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12814 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12814 0.011 Θ ∧ gammaRatio 12814 0.011 Θ ≤ 0.000085806569 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12814 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035648178532 : ℝ) * 0.525 / ((1 - 0.011) * 12814) := by gcongr
      _ ≤ (0.000085806569 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12814 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12814 0.011 Θ) :=
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
    badAllowance 12814 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12814 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12814 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12814 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12814 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12814 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12814 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12814 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12814 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12814 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12814 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035648178532 : ℝ) * 12814 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12814 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003398838315 + 0.003263354344 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12814

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12814
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12814 BstLean.Part154.csC) (piBar (rhoBar 12814 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12814 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12814 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12814 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12814 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12814 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12814 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12814 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12814 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12814 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12814 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12814 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12814 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12814 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12814 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052247801464 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12814) ≤ 0.010549900749 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12814 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035648178532)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010549900749 + 2 * 0.737676 / 12814) := by gcongr
    _ ≤ (0.052247801464 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12814 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12814

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12814
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508677844 : ℝ) ≤ plow 12814 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12814) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052618699346)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367672689) : eMP 12814 0.011 xi bn ≤ 0.001177586971 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12814 : ℝ) * (1 - 0.011))) ≤ 0.000582271512 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001367672689 / (12814 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582271512 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582271512 : ℝ) + 3.141593 * 0.052618699346 / (12814 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001177586971 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052618699346)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367672689) : PiBarMP 12814 12 0.011 xi bn ≤ 0.160524808612 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12814 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036982059016 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.574624138835 : ℝ) ≤ √((12814 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.198939924365 : ℝ) ≤ √(12814 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12814) ≤ 0.123078964097 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036982059016 + 0.052618699346 * 1.772454 / (2 * (112.574624138835 : ℝ))) * (1 + 0.001177586971) +
        8 / (12814 * 113.198939924365) + 0.123078964097 := by gcongr
    _ ≤ (0.160524808612 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052618699346)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367672689) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281635463177) :
    parallelOracle 12814 0.011 xi bn cd ≤ 0.161506132480 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12814 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12814 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508677844 : ℝ) ≤ plow 12814 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.198939924365 : ℝ) ≤ √(12814 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281635463177 : ℝ) / (2 * 0.560508677844 * 113.198939924365)) * 0.160524808612 +
        0.281635463177 ^ 2 / (2 * 0.560508677844 * 113.198939924365) := by gcongr
    _ ≤ (0.161506132480 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052618699346) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367672689)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281635463177) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12814 12814 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508677844 : ℝ) ≤ plow 12814 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.198939924365 : ℝ) ≤ √(12814 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12814 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12814 Θ 1.22 ≤ 0.011714778433 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.198939924365 := by gcongr <;> linarith
      _ ≤ (0.011714778433 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12814 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12814 12814 0.011 ≤ 0.008444310495 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12814 12814 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12814 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12814 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12814 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12814 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161506132480 + 0.011714778433 + (0.008444310495 : ℝ) *
        (1 + 2 * (0.281635463177 + 0.011714778433) / (0.560508677844 * 113.198939924365))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12814]

end BstLean.Part269.N12814

/-! The original eight local profiles supply actual 12814 moment certificates. -/
namespace BstLean.Part269.N12814
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12814 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12814 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12814 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052618699346 ∧
    0 ≤ bN 12814 BstLean.Part154.csC (groupTheta g) ∧ bN 12814 BstLean.Part154.csC (groupTheta g) ≤ 0.001367672689 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12814 12814 0.011
      (momentAllowance 12814 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12814 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12814 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12814 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12814 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12814 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229387661713 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12814 0.011
      (momentAllowance 12814 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12814 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12814
/-! The actual computed-centre upper energy formula at 12814. -/
namespace BstLean.Part269.N12814
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12814

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12814
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12814)
open BstLean.Part268 (cell12814)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085164580663
  | 2 => 0.086101497349
  | 3 => 0.087035727371
  | 4 => 0.087968496752
  | 5 => 0.088901294488
  | 6 => 0.089835912382
  | 7 => 0.090774488764
  | 8 => 0.091719556180
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12814 12814 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12814 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12814

/-! Actual upper energy certificates on all 43 source endpoints at 12814. -/
namespace BstLean.Part269.N12814
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12814)
open BstLean.Part268 (cell12814)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12814 (gMinus 12814) (1 - (cell12814 i).lower) ≤ 1 ∧
    energyUpper 12814 (gMinus 12814) (BstLean.Part211.gPlus 12814)
      (finiteEnergy 12814 12814 0.011) (1 - (cell12814 i).lower) ≤
      (cell12814 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨10,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨11,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨12,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨13,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨14,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨15,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨16,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨17,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨18,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨19,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨20,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨21,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨22,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨23,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨24,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨25,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨26,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨27,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨28,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨29,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨30,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨31,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨32,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨33,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨34,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨35,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨36,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨37,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨38,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨39,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨40,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨41,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨42,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨43,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨44,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨45,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨46,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨47,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨48,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨49,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨50,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨51,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12814) (by norm_num)
        (q := 1 - (cell12814 ⟨52,by decide⟩).lower)
        (by norm_num [cell12814]) (by norm_num [cell12814])
      exact ⟨E.1,E.2.trans (by norm_num [cell12814])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12814

/-! Source-cell containment and simple scalar guards at 12814. -/
namespace BstLean.Part269.N12814
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12814)
open BstLean.Part268 (cell12814)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12814 ⟨10,by decide⟩).lower ∧ (cell12814 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12814 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12814 ⟨11,by decide⟩).lower ∧ (cell12814 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12814 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12814 ⟨12,by decide⟩).lower ∧ (cell12814 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12814 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12814 ⟨13,by decide⟩).lower ∧ (cell12814 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12814 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12814 ⟨14,by decide⟩).lower ∧ (cell12814 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12814 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12814 ⟨15,by decide⟩).lower ∧ (cell12814 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12814 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12814 ⟨16,by decide⟩).lower ∧ (cell12814 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12814 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12814 ⟨17,by decide⟩).lower ∧ (cell12814 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12814 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12814 ⟨18,by decide⟩).lower ∧ (cell12814 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12814 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12814 ⟨19,by decide⟩).lower ∧ (cell12814 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12814 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12814 ⟨20,by decide⟩).lower ∧ (cell12814 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12814 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12814 ⟨21,by decide⟩).lower ∧ (cell12814 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12814 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12814 ⟨22,by decide⟩).lower ∧ (cell12814 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12814 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12814 ⟨23,by decide⟩).lower ∧ (cell12814 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12814 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12814 ⟨24,by decide⟩).lower ∧ (cell12814 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12814 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12814 ⟨25,by decide⟩).lower ∧ (cell12814 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12814 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12814 ⟨26,by decide⟩).lower ∧ (cell12814 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12814 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12814 ⟨27,by decide⟩).lower ∧ (cell12814 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12814 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12814 ⟨28,by decide⟩).lower ∧ (cell12814 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12814 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12814 ⟨29,by decide⟩).lower ∧ (cell12814 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12814 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12814 ⟨30,by decide⟩).lower ∧ (cell12814 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12814 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12814 ⟨31,by decide⟩).lower ∧ (cell12814 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12814 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12814 ⟨32,by decide⟩).lower ∧ (cell12814 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12814 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12814 ⟨33,by decide⟩).lower ∧ (cell12814 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12814 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12814 ⟨34,by decide⟩).lower ∧ (cell12814 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12814 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12814 ⟨35,by decide⟩).lower ∧ (cell12814 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12814 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12814 ⟨36,by decide⟩).lower ∧ (cell12814 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12814 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12814 ⟨37,by decide⟩).lower ∧ (cell12814 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12814 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12814 ⟨38,by decide⟩).lower ∧ (cell12814 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12814 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12814 ⟨39,by decide⟩).lower ∧ (cell12814 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12814 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12814 ⟨40,by decide⟩).lower ∧ (cell12814 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12814 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12814 ⟨41,by decide⟩).lower ∧ (cell12814 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12814 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12814 ⟨42,by decide⟩).lower ∧ (cell12814 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12814 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12814 ⟨43,by decide⟩).lower ∧ (cell12814 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12814 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12814 ⟨44,by decide⟩).lower ∧ (cell12814 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12814 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12814 ⟨45,by decide⟩).lower ∧ (cell12814 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12814 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12814 ⟨46,by decide⟩).lower ∧ (cell12814 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12814 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12814 ⟨47,by decide⟩).lower ∧ (cell12814 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12814 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12814 ⟨48,by decide⟩).lower ∧ (cell12814 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12814 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12814 ⟨49,by decide⟩).lower ∧ (cell12814 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12814 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12814 ⟨50,by decide⟩).lower ∧ (cell12814 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12814 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12814 ⟨51,by decide⟩).lower ∧ (cell12814 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12814 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12814 ⟨52,by decide⟩).lower ∧ (cell12814 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12814 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12814 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12814 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12814,cell12814,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12814 i).lower ∧
    (cell12814 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12814 i).upper ≤ (0.532 : ℝ) ∧
    (cell12814 i).centre ≤ (0.1 : ℝ) ∧ (cell12814 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12814 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12814 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12814

/-! The local source numeric instances at 12814 have no network premises. -/
namespace BstLean.Part269.N12814
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12814)
open BstLean.Part268 (cell12814)

noncomputable def sourceNumerics12814 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12814 (cell12814 i)
      scalarRow12814.M scalarRow12814.H scalarRow12814.xi := by
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
    energy_allowance := scalarRow12814.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12814]
    centre_nonneg := (scalarRow12814.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12814])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12814
/-! Actual 12815 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12815
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12815 ≤ (1.035646775448 : ℝ) := by
  have hr : (113.203356840687 : ℝ) ≤ √(12815 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.203356840687 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12815 12815 (11 / 1000) ≤
    (0.008443981016 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12815) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.203356840687 : ℝ) ≤ √(12815 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12815)
  have hdiv : K / √(12815 : ℝ) ≤ K / 113.203356840687 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.203356840687 ≤ (0.008443981016 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12815.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12815 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12815 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12815 := gPlus_lower 12815
end BstLean.Part269.N12815

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12815
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035646775447 : ℝ) ≤ wn 12815 := by
  have hn : √(12815 : ℝ) ≤ 113.203356840688 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12815 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.203356840688 ≤ 2 / √(12815 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249581378 : ℝ) ≤ rhoBar 12815 BstLean.Part154.csC ∧
    rhoBar 12815 BstLean.Part154.csC ≤ 0.000249581764 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035646775447 : ℝ) / (1.295212 * 12815) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035646775448 : ℝ) / (1.29521 * 12815) := by gcongr
      _ ≤ (0.000249581764 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12815 BstLean.Part154.csC) ≤ 0.000998389348 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12815 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12815 BstLean.Part154.csC) (piBar (rhoBar 12815 BstLean.Part154.csC)) ≤ 0.000190632154 ∧
    cc1 (rhoBar 12815 BstLean.Part154.csC) (piBar (rhoBar 12815 BstLean.Part154.csC)) ≤ 0.000121300522 ∧
    cc2 (rhoBar 12815 BstLean.Part154.csC) ≤ 0.000070415903 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12815 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12815 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12815 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12815 BstLean.Part154.csC * nuR (rhoBar 12815 BstLean.Part154.csC)) ≤ 0.000499179101 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249581764 : ℝ) * 0.000998389348 := by gcongr
      _ ≤ (0.000499179101 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12815 BstLean.Part154.csC) * nuR (rhoBar 12815 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000998389348 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12815 BstLean.Part154.csC) * rhoBar 12815 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249581764 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249581764 / 2 + 0.399 * 0.000998389348 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190632154 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499179101 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121300522 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249581764 / 1.414213562 := by gcongr
      _ ≤ (0.000070415903 : ℝ) := by norm_num

end BstLean.Part269.N12815

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12815
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12815 BstLean.Part154.csC) (piBar (rhoBar 12815 BstLean.Part154.csC)) ≤ 1.56938E-7 := by
  have hr0 : 0 ≤ rhoBar 12815 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12815 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12815 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12815 BstLean.Part154.csC) (piBar (rhoBar 12815 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12815 BstLean.Part154.csC) (piBar (rhoBar 12815 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12815 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190632154 : ℝ) ^ 2 + 0.000121300522 ^ 2 + 3 * 0.000070415903 ^ 2 +
        2 * 0.797885 * 0.000190632154 * 0.000121300522 + 2 * 0.000190632154 * 0.000070415903 +
        4 * 0.797885 * 0.000121300522 * 0.000070415903 := by gcongr
    _ ≤ (1.56938E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12815 BstLean.Part154.csC Θ ≤ 0.002604879178 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12815 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12815 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12815 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12815 BstLean.Part154.csC) (piBar (rhoBar 12815 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12815 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035646775448 * 1.56938E-7 / (0.000249581378 : ℝ) := by gcongr
    _ ≤ 0.002604879178 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12815 BstLean.Part154.csC Θ ≤ 0.002889796525 + 0.000658210358 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12815 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12815 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12815 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035646775448 : ℝ) * ((2 * Θ * 0.000249581764 +
        (6863 / 10000) * 0.000249581764 * 12815 * 0.000998389348) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002889796525 + 0.000658210358 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12815 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12815 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12815 0.011 Θ ∧ gammaRatio 12815 0.011 Θ ≤ 0.000085799757 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12815 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035646775448 : ℝ) * 0.525 / ((1 - 0.011) * 12815) := by gcongr
      _ ≤ (0.000085799757 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12815 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12815 0.011 Θ) :=
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
    badAllowance 12815 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12815 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12815 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12815 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12815 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12815 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12815 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12815 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12815 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12815 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12815 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035646775448 : ℝ) * 12815 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12815 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003398601025 + 0.003263089536 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12815

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12815
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12815 BstLean.Part154.csC) (piBar (rhoBar 12815 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12815 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12815 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12815 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12815 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12815 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12815 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12815 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12815 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12815 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12815 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12815 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12815 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12815 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12815 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052245740877 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12815) ≤ 0.010549489118 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12815 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035646775448)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010549489118 + 2 * 0.737676 / 12815) := by gcongr
    _ ≤ (0.052245740877 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12815 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12815

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12815
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508722262 : ℝ) ≤ plow 12815 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12815) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052618323032)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367561569) : eMP 12815 0.011 xi bn ≤ 0.001177493114 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12815 : ℝ) * (1 - 0.011))) ≤ 0.000582225139 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001367561569 / (12815 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582225139 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582225139 : ℝ) + 3.141593 * 0.052618323032 / (12815 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001177493114 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052618323032)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367561569) : PiBarMP 12815 12 0.011 xi bn ≤ 0.160518478921 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12815 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036980556635 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.579016694941 : ℝ) ≤ √((12815 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.203356840687 : ℝ) ≤ √(12815 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12815) ≤ 0.123074161859 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036980556635 + 0.052618323032 * 1.772454 / (2 * (112.579016694941 : ℝ))) * (1 + 0.001177493114) +
        8 / (12815 * 113.203356840687) + 0.123074161859 := by gcongr
    _ ≤ (0.160518478921 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052618323032)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367561569) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281632582331) :
    parallelOracle 12815 0.011 xi bn cd ≤ 0.161499733945 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12815 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12815 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508722262 : ℝ) ≤ plow 12815 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.203356840687 : ℝ) ≤ √(12815 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281632582331 : ℝ) / (2 * 0.560508722262 * 113.203356840687)) * 0.160518478921 +
        0.281632582331 ^ 2 / (2 * 0.560508722262 * 113.203356840687) := by gcongr
    _ ≤ (0.161499733945 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052618323032) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367561569)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281632582331) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12815 12815 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508722262 : ℝ) ≤ plow 12815 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.203356840687 : ℝ) ≤ √(12815 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12815 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12815 Θ 1.22 ≤ 0.011714321351 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.203356840687 := by gcongr <;> linarith
      _ ≤ (0.011714321351 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12815 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12815 12815 0.011 ≤ 0.008443981016 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12815 12815 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12815 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12815 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12815 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12815 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161499733945 + 0.011714321351 + (0.008443981016 : ℝ) *
        (1 + 2 * (0.281632582331 + 0.011714321351) / (0.560508722262 * 113.203356840687))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12815]

end BstLean.Part269.N12815

/-! The original eight local profiles supply actual 12815 moment certificates. -/
namespace BstLean.Part269.N12815
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12815 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12815 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12815 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052618323032 ∧
    0 ≤ bN 12815 BstLean.Part154.csC (groupTheta g) ∧ bN 12815 BstLean.Part154.csC (groupTheta g) ≤ 0.001367561569 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12815 12815 0.011
      (momentAllowance 12815 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12815 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12815 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12815 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12815 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12815 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229386841454 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12815 0.011
      (momentAllowance 12815 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12815 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12815
/-! The actual computed-centre upper energy formula at 12815. -/
namespace BstLean.Part269.N12815
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12815

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12815
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12815)
open BstLean.Part268 (cell12815)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085161781624
  | 2 => 0.086098649466
  | 3 => 0.087032823941
  | 4 => 0.087965529500
  | 5 => 0.088898253285
  | 6 => 0.089832784923
  | 7 => 0.090771260216
  | 8 => 0.091716208780
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12815 12815 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12815 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12815

/-! Actual upper energy certificates on all 43 source endpoints at 12815. -/
namespace BstLean.Part269.N12815
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12815)
open BstLean.Part268 (cell12815)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12815 (gMinus 12815) (1 - (cell12815 i).lower) ≤ 1 ∧
    energyUpper 12815 (gMinus 12815) (BstLean.Part211.gPlus 12815)
      (finiteEnergy 12815 12815 0.011) (1 - (cell12815 i).lower) ≤
      (cell12815 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨10,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨11,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨12,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨13,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨14,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨15,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨16,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨17,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨18,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨19,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨20,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨21,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨22,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨23,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨24,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨25,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨26,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨27,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨28,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨29,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨30,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨31,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨32,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨33,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨34,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨35,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨36,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨37,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨38,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨39,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨40,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨41,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨42,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨43,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨44,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨45,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨46,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨47,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨48,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨49,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨50,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨51,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12815) (by norm_num)
        (q := 1 - (cell12815 ⟨52,by decide⟩).lower)
        (by norm_num [cell12815]) (by norm_num [cell12815])
      exact ⟨E.1,E.2.trans (by norm_num [cell12815])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12815

/-! Source-cell containment and simple scalar guards at 12815. -/
namespace BstLean.Part269.N12815
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12815)
open BstLean.Part268 (cell12815)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12815 ⟨10,by decide⟩).lower ∧ (cell12815 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12815 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12815 ⟨11,by decide⟩).lower ∧ (cell12815 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12815 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12815 ⟨12,by decide⟩).lower ∧ (cell12815 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12815 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12815 ⟨13,by decide⟩).lower ∧ (cell12815 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12815 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12815 ⟨14,by decide⟩).lower ∧ (cell12815 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12815 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12815 ⟨15,by decide⟩).lower ∧ (cell12815 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12815 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12815 ⟨16,by decide⟩).lower ∧ (cell12815 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12815 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12815 ⟨17,by decide⟩).lower ∧ (cell12815 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12815 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12815 ⟨18,by decide⟩).lower ∧ (cell12815 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12815 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12815 ⟨19,by decide⟩).lower ∧ (cell12815 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12815 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12815 ⟨20,by decide⟩).lower ∧ (cell12815 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12815 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12815 ⟨21,by decide⟩).lower ∧ (cell12815 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12815 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12815 ⟨22,by decide⟩).lower ∧ (cell12815 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12815 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12815 ⟨23,by decide⟩).lower ∧ (cell12815 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12815 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12815 ⟨24,by decide⟩).lower ∧ (cell12815 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12815 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12815 ⟨25,by decide⟩).lower ∧ (cell12815 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12815 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12815 ⟨26,by decide⟩).lower ∧ (cell12815 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12815 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12815 ⟨27,by decide⟩).lower ∧ (cell12815 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12815 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12815 ⟨28,by decide⟩).lower ∧ (cell12815 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12815 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12815 ⟨29,by decide⟩).lower ∧ (cell12815 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12815 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12815 ⟨30,by decide⟩).lower ∧ (cell12815 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12815 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12815 ⟨31,by decide⟩).lower ∧ (cell12815 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12815 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12815 ⟨32,by decide⟩).lower ∧ (cell12815 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12815 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12815 ⟨33,by decide⟩).lower ∧ (cell12815 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12815 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12815 ⟨34,by decide⟩).lower ∧ (cell12815 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12815 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12815 ⟨35,by decide⟩).lower ∧ (cell12815 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12815 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12815 ⟨36,by decide⟩).lower ∧ (cell12815 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12815 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12815 ⟨37,by decide⟩).lower ∧ (cell12815 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12815 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12815 ⟨38,by decide⟩).lower ∧ (cell12815 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12815 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12815 ⟨39,by decide⟩).lower ∧ (cell12815 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12815 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12815 ⟨40,by decide⟩).lower ∧ (cell12815 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12815 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12815 ⟨41,by decide⟩).lower ∧ (cell12815 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12815 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12815 ⟨42,by decide⟩).lower ∧ (cell12815 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12815 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12815 ⟨43,by decide⟩).lower ∧ (cell12815 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12815 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12815 ⟨44,by decide⟩).lower ∧ (cell12815 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12815 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12815 ⟨45,by decide⟩).lower ∧ (cell12815 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12815 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12815 ⟨46,by decide⟩).lower ∧ (cell12815 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12815 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12815 ⟨47,by decide⟩).lower ∧ (cell12815 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12815 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12815 ⟨48,by decide⟩).lower ∧ (cell12815 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12815 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12815 ⟨49,by decide⟩).lower ∧ (cell12815 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12815 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12815 ⟨50,by decide⟩).lower ∧ (cell12815 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12815 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12815 ⟨51,by decide⟩).lower ∧ (cell12815 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12815 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12815 ⟨52,by decide⟩).lower ∧ (cell12815 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12815 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12815 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12815 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12815,cell12815,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12815 i).lower ∧
    (cell12815 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12815 i).upper ≤ (0.532 : ℝ) ∧
    (cell12815 i).centre ≤ (0.1 : ℝ) ∧ (cell12815 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12815 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12815 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12815

/-! The local source numeric instances at 12815 have no network premises. -/
namespace BstLean.Part269.N12815
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12815)
open BstLean.Part268 (cell12815)

noncomputable def sourceNumerics12815 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12815 (cell12815 i)
      scalarRow12815.M scalarRow12815.H scalarRow12815.xi := by
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
    energy_allowance := scalarRow12815.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12815]
    centre_nonneg := (scalarRow12815.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12815])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12815
/-! Actual 12816 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12816
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12816 ≤ (1.035645372530 : ℝ) := by
  have hr : (113.207773584679 : ℝ) ≤ √(12816 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.207773584679 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12816 12816 (11 / 1000) ≤
    (0.008443651576 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12816) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.207773584679 : ℝ) ≤ √(12816 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12816)
  have hdiv : K / √(12816 : ℝ) ≤ K / 113.207773584679 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.207773584679 ≤ (0.008443651576 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12816.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12816 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12816 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12816 := gPlus_lower 12816
end BstLean.Part269.N12816

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12816
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035645372529 : ℝ) ≤ wn 12816 := by
  have hn : √(12816 : ℝ) ≤ 113.207773584680 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12816 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.207773584680 ≤ 2 / √(12816 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249561565 : ℝ) ≤ rhoBar 12816 BstLean.Part154.csC ∧
    rhoBar 12816 BstLean.Part154.csC ≤ 0.000249561952 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035645372529 : ℝ) / (1.295212 * 12816) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035645372530 : ℝ) / (1.29521 * 12816) := by gcongr
      _ ≤ (0.000249561952 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12816 BstLean.Part154.csC) ≤ 0.000998310090 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12816 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12816 BstLean.Part154.csC) (piBar (rhoBar 12816 BstLean.Part154.csC)) ≤ 0.000190617021 ∧
    cc1 (rhoBar 12816 BstLean.Part154.csC) (piBar (rhoBar 12816 BstLean.Part154.csC)) ≤ 0.000121290893 ∧
    cc2 (rhoBar 12816 BstLean.Part154.csC) ≤ 0.000070410313 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12816 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12816 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12816 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12816 BstLean.Part154.csC * nuR (rhoBar 12816 BstLean.Part154.csC)) ≤ 0.000499139475 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249561952 : ℝ) * 0.000998310090 := by gcongr
      _ ≤ (0.000499139475 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12816 BstLean.Part154.csC) * nuR (rhoBar 12816 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000998310090 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12816 BstLean.Part154.csC) * rhoBar 12816 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249561952 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249561952 / 2 + 0.399 * 0.000998310090 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190617021 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499139475 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121290893 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249561952 / 1.414213562 := by gcongr
      _ ≤ (0.000070410313 : ℝ) := by norm_num

end BstLean.Part269.N12816

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12816
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12816 BstLean.Part154.csC) (piBar (rhoBar 12816 BstLean.Part154.csC)) ≤ 1.56913E-7 := by
  have hr0 : 0 ≤ rhoBar 12816 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12816 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12816 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12816 BstLean.Part154.csC) (piBar (rhoBar 12816 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12816 BstLean.Part154.csC) (piBar (rhoBar 12816 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12816 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190617021 : ℝ) ^ 2 + 0.000121290893 ^ 2 + 3 * 0.000070410313 ^ 2 +
        2 * 0.797885 * 0.000190617021 * 0.000121290893 + 2 * 0.000190617021 * 0.000070410313 +
        4 * 0.797885 * 0.000121290893 * 0.000070410313 := by gcongr
    _ ≤ (1.56913E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12816 BstLean.Part154.csC Θ ≤ 0.002604667467 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12816 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12816 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12816 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12816 BstLean.Part154.csC) (piBar (rhoBar 12816 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12816 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035645372530 * 1.56913E-7 / (0.000249561565 : ℝ) := by gcongr
    _ ≤ 0.002604667467 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12816 BstLean.Part154.csC Θ ≤ 0.002889559291 + 0.000658157217 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12816 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12816 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12816 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035645372530 : ℝ) * ((2 * Θ * 0.000249561952 +
        (6863 / 10000) * 0.000249561952 * 12816 * 0.000998310090) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002889559291 + 0.000658157217 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12816 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12816 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12816 0.011 Θ ∧ gammaRatio 12816 0.011 Θ ≤ 0.000085792946 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12816 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035645372530 : ℝ) * 0.525 / ((1 - 0.011) * 12816) := by gcongr
      _ ≤ (0.000085792946 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12816 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12816 0.011 Θ) :=
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
    badAllowance 12816 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12816 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12816 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12816 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12816 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12816 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12816 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12816 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12816 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12816 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12816 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035645372530 : ℝ) * 12816 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12816 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003398363791 + 0.003262824684 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12816

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12816
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12816 BstLean.Part154.csC) (piBar (rhoBar 12816 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12816 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12816 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12816 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12816 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12816 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12816 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12816 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12816 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12816 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12816 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12816 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12816 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12816 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12816 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052243680532 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12816) ≤ 0.010549077535 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12816 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035645372530)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010549077535 + 2 * 0.737676 / 12816) := by gcongr
    _ ≤ (0.052243680532 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12816 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12816

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12816
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508766674 : ℝ) ≤ plow 12816 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12816) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052617946751)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367450421) : eMP 12816 0.011 xi bn ≤ 0.001177399255 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12816 : ℝ) * (1 - 0.011))) ≤ 0.000582178765 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001367450421 / (12816 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582178765 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582178765 : ℝ) + 3.141593 * 0.052617946751 / (12816 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001177399255 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052617946751)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367450421) : PiBarMP 12816 12 0.011 xi bn ≤ 0.160512149356 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12816 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036979053815 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.583409079668 : ℝ) ≤ √((12816 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.207773584679 : ℝ) ≤ √(12816 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12816) ≤ 0.123069360183 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036979053815 + 0.052617946751 * 1.772454 / (2 * (112.583409079668 : ℝ))) * (1 + 0.001177399255) +
        8 / (12816 * 113.207773584679) + 0.123069360183 := by gcongr
    _ ≤ (0.160512149356 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052617946751)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367450421) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281629701796) :
    parallelOracle 12816 0.011 xi bn cd ≤ 0.161493335544 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12816 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12816 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508766674 : ℝ) ≤ plow 12816 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.207773584679 : ℝ) ≤ √(12816 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281629701796 : ℝ) / (2 * 0.560508766674 * 113.207773584679)) * 0.160512149356 +
        0.281629701796 ^ 2 / (2 * 0.560508766674 * 113.207773584679) := by gcongr
    _ ≤ (0.161493335544 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052617946751) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367450421)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281629701796) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12816 12816 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508766674 : ℝ) ≤ plow 12816 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.207773584679 : ℝ) ≤ √(12816 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12816 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12816 Θ 1.22 ≤ 0.011713864323 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.207773584679 := by gcongr <;> linarith
      _ ≤ (0.011713864323 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12816 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12816 12816 0.011 ≤ 0.008443651576 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12816 12816 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12816 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12816 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12816 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12816 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161493335544 + 0.011713864323 + (0.008443651576 : ℝ) *
        (1 + 2 * (0.281629701796 + 0.011713864323) / (0.560508766674 * 113.207773584679))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12816]

end BstLean.Part269.N12816

/-! The original eight local profiles supply actual 12816 moment certificates. -/
namespace BstLean.Part269.N12816
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12816 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12816 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12816 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052617946751 ∧
    0 ≤ bN 12816 BstLean.Part154.csC (groupTheta g) ∧ bN 12816 BstLean.Part154.csC (groupTheta g) ≤ 0.001367450421 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12816 12816 0.011
      (momentAllowance 12816 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12816 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12816 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12816 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12816 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12816 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229386021264 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12816 0.011
      (momentAllowance 12816 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12816 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12816
/-! The actual computed-centre upper energy formula at 12816. -/
namespace BstLean.Part269.N12816
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12816

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12816
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12816)
open BstLean.Part268 (cell12816)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085158983552
  | 2 => 0.086095802589
  | 3 => 0.087029921564
  | 4 => 0.087962563359
  | 5 => 0.088895213263
  | 6 => 0.089829658732
  | 7 => 0.090768033041
  | 8 => 0.091712862881
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12816 12816 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12816 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12816

/-! Actual upper energy certificates on all 43 source endpoints at 12816. -/
namespace BstLean.Part269.N12816
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12816)
open BstLean.Part268 (cell12816)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12816 (gMinus 12816) (1 - (cell12816 i).lower) ≤ 1 ∧
    energyUpper 12816 (gMinus 12816) (BstLean.Part211.gPlus 12816)
      (finiteEnergy 12816 12816 0.011) (1 - (cell12816 i).lower) ≤
      (cell12816 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨10,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨11,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨12,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨13,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨14,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨15,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨16,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨17,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨18,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨19,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨20,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨21,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨22,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨23,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨24,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨25,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨26,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨27,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨28,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨29,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨30,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨31,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨32,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨33,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨34,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨35,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨36,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨37,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨38,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨39,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨40,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨41,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨42,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨43,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨44,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨45,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨46,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨47,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨48,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨49,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨50,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨51,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12816) (by norm_num)
        (q := 1 - (cell12816 ⟨52,by decide⟩).lower)
        (by norm_num [cell12816]) (by norm_num [cell12816])
      exact ⟨E.1,E.2.trans (by norm_num [cell12816])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12816

/-! Source-cell containment and simple scalar guards at 12816. -/
namespace BstLean.Part269.N12816
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12816)
open BstLean.Part268 (cell12816)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12816 ⟨10,by decide⟩).lower ∧ (cell12816 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12816 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12816 ⟨11,by decide⟩).lower ∧ (cell12816 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12816 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12816 ⟨12,by decide⟩).lower ∧ (cell12816 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12816 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12816 ⟨13,by decide⟩).lower ∧ (cell12816 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12816 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12816 ⟨14,by decide⟩).lower ∧ (cell12816 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12816 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12816 ⟨15,by decide⟩).lower ∧ (cell12816 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12816 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12816 ⟨16,by decide⟩).lower ∧ (cell12816 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12816 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12816 ⟨17,by decide⟩).lower ∧ (cell12816 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12816 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12816 ⟨18,by decide⟩).lower ∧ (cell12816 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12816 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12816 ⟨19,by decide⟩).lower ∧ (cell12816 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12816 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12816 ⟨20,by decide⟩).lower ∧ (cell12816 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12816 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12816 ⟨21,by decide⟩).lower ∧ (cell12816 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12816 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12816 ⟨22,by decide⟩).lower ∧ (cell12816 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12816 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12816 ⟨23,by decide⟩).lower ∧ (cell12816 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12816 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12816 ⟨24,by decide⟩).lower ∧ (cell12816 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12816 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12816 ⟨25,by decide⟩).lower ∧ (cell12816 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12816 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12816 ⟨26,by decide⟩).lower ∧ (cell12816 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12816 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12816 ⟨27,by decide⟩).lower ∧ (cell12816 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12816 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12816 ⟨28,by decide⟩).lower ∧ (cell12816 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12816 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12816 ⟨29,by decide⟩).lower ∧ (cell12816 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12816 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12816 ⟨30,by decide⟩).lower ∧ (cell12816 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12816 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12816 ⟨31,by decide⟩).lower ∧ (cell12816 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12816 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12816 ⟨32,by decide⟩).lower ∧ (cell12816 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12816 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12816 ⟨33,by decide⟩).lower ∧ (cell12816 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12816 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12816 ⟨34,by decide⟩).lower ∧ (cell12816 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12816 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12816 ⟨35,by decide⟩).lower ∧ (cell12816 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12816 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12816 ⟨36,by decide⟩).lower ∧ (cell12816 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12816 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12816 ⟨37,by decide⟩).lower ∧ (cell12816 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12816 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12816 ⟨38,by decide⟩).lower ∧ (cell12816 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12816 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12816 ⟨39,by decide⟩).lower ∧ (cell12816 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12816 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12816 ⟨40,by decide⟩).lower ∧ (cell12816 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12816 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12816 ⟨41,by decide⟩).lower ∧ (cell12816 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12816 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12816 ⟨42,by decide⟩).lower ∧ (cell12816 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12816 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12816 ⟨43,by decide⟩).lower ∧ (cell12816 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12816 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12816 ⟨44,by decide⟩).lower ∧ (cell12816 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12816 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12816 ⟨45,by decide⟩).lower ∧ (cell12816 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12816 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12816 ⟨46,by decide⟩).lower ∧ (cell12816 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12816 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12816 ⟨47,by decide⟩).lower ∧ (cell12816 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12816 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12816 ⟨48,by decide⟩).lower ∧ (cell12816 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12816 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12816 ⟨49,by decide⟩).lower ∧ (cell12816 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12816 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12816 ⟨50,by decide⟩).lower ∧ (cell12816 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12816 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12816 ⟨51,by decide⟩).lower ∧ (cell12816 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12816 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12816 ⟨52,by decide⟩).lower ∧ (cell12816 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12816 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12816 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12816 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12816,cell12816,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12816 i).lower ∧
    (cell12816 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12816 i).upper ≤ (0.532 : ℝ) ∧
    (cell12816 i).centre ≤ (0.1 : ℝ) ∧ (cell12816 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12816 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12816 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12816

/-! The local source numeric instances at 12816 have no network premises. -/
namespace BstLean.Part269.N12816
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12816)
open BstLean.Part268 (cell12816)

noncomputable def sourceNumerics12816 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12816 (cell12816 i)
      scalarRow12816.M scalarRow12816.H scalarRow12816.xi := by
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
    energy_allowance := scalarRow12816.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12816]
    centre_nonneg := (scalarRow12816.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12816])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12816
/-! Actual 12817 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12817
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12817 ≤ (1.035643969777 : ℝ) := by
  have hr : (113.212190156360 : ℝ) ≤ √(12817 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.212190156360 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12817 12817 (11 / 1000) ≤
    (0.008443322175 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12817) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.212190156360 : ℝ) ≤ √(12817 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12817)
  have hdiv : K / √(12817 : ℝ) ≤ K / 113.212190156360 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.212190156360 ≤ (0.008443322175 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12817.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12817 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12817 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12817 := gPlus_lower 12817
end BstLean.Part269.N12817

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12817
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035643969776 : ℝ) ≤ wn 12817 := by
  have hn : √(12817 : ℝ) ≤ 113.212190156361 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12817 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.212190156361 ≤ 2 / √(12817 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249541756 : ℝ) ≤ rhoBar 12817 BstLean.Part154.csC ∧
    rhoBar 12817 BstLean.Part154.csC ≤ 0.000249542143 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035643969776 : ℝ) / (1.295212 * 12817) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035643969777 : ℝ) / (1.29521 * 12817) := by gcongr
      _ ≤ (0.000249542143 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12817 BstLean.Part154.csC) ≤ 0.000998230844 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12817 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12817 BstLean.Part154.csC) (piBar (rhoBar 12817 BstLean.Part154.csC)) ≤ 0.000190601890 ∧
    cc1 (rhoBar 12817 BstLean.Part154.csC) (piBar (rhoBar 12817 BstLean.Part154.csC)) ≤ 0.000121281265 ∧
    cc2 (rhoBar 12817 BstLean.Part154.csC) ≤ 0.000070404724 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12817 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12817 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12817 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12817 BstLean.Part154.csC * nuR (rhoBar 12817 BstLean.Part154.csC)) ≤ 0.000499099854 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249542143 : ℝ) * 0.000998230844 := by gcongr
      _ ≤ (0.000499099854 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12817 BstLean.Part154.csC) * nuR (rhoBar 12817 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000998230844 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12817 BstLean.Part154.csC) * rhoBar 12817 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249542143 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249542143 / 2 + 0.399 * 0.000998230844 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190601890 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499099854 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121281265 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249542143 / 1.414213562 := by gcongr
      _ ≤ (0.000070404724 : ℝ) := by norm_num

end BstLean.Part269.N12817

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12817
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12817 BstLean.Part154.csC) (piBar (rhoBar 12817 BstLean.Part154.csC)) ≤ 1.56888E-7 := by
  have hr0 : 0 ≤ rhoBar 12817 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12817 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12817 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12817 BstLean.Part154.csC) (piBar (rhoBar 12817 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12817 BstLean.Part154.csC) (piBar (rhoBar 12817 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12817 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190601890 : ℝ) ^ 2 + 0.000121281265 ^ 2 + 3 * 0.000070404724 ^ 2 +
        2 * 0.797885 * 0.000190601890 * 0.000121281265 + 2 * 0.000190601890 * 0.000070404724 +
        4 * 0.797885 * 0.000121281265 * 0.000070404724 := by gcongr
    _ ≤ (1.56888E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12817 BstLean.Part154.csC Θ ≤ 0.002604455683 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12817 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12817 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12817 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12817 BstLean.Part154.csC) (piBar (rhoBar 12817 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12817 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035643969777 * 1.56888E-7 / (0.000249541756 : ℝ) := by gcongr
    _ ≤ 0.002604455683 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12817 BstLean.Part154.csC Θ ≤ 0.002889322092 + 0.000658104084 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12817 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12817 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12817 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035643969777 : ℝ) * ((2 * Θ * 0.000249542143 +
        (6863 / 10000) * 0.000249542143 * 12817 * 0.000998230844) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002889322092 + 0.000658104084 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12817 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12817 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12817 0.011 Θ ∧ gammaRatio 12817 0.011 Θ ≤ 0.000085786136 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12817 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035643969777 : ℝ) * 0.525 / ((1 - 0.011) * 12817) := by gcongr
      _ ≤ (0.000085786136 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12817 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12817 0.011 Θ) :=
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
    badAllowance 12817 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12817 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12817 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12817 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12817 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12817 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12817 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12817 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12817 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12817 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12817 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035643969777 : ℝ) * 12817 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12817 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003398126592 + 0.003262559767 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12817

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12817
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12817 BstLean.Part154.csC) (piBar (rhoBar 12817 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12817 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12817 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12817 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12817 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12817 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12817 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12817 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12817 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12817 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12817 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12817 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12817 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12817 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12817 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052241620430 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12817) ≤ 0.010548666000 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12817 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035643969777)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010548666000 + 2 * 0.737676 / 12817) := by gcongr
    _ ≤ (0.052241620430 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12817 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12817

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12817
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508811079 : ℝ) ≤ plow 12817 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12817) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052617570470)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367339234) : eMP 12817 0.011 xi bn ≤ 0.001177305384 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12817 : ℝ) * (1 - 0.011))) ≤ 0.000582132385 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001367339234 / (12817 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582132385 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582132385 : ℝ) + 3.141593 * 0.052617570470 / (12817 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001177305384 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052617570470)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367339234) : PiBarMP 12817 12 0.011 xi bn ≤ 0.160505819765 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12817 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036977550406 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.587801293035 : ℝ) ≤ √((12817 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.212190156360 : ℝ) ≤ √(12817 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12817) ≤ 0.123064559069 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036977550406 + 0.052617570470 * 1.772454 / (2 * (112.587801293035 : ℝ))) * (1 + 0.001177305384) +
        8 / (12817 * 113.212190156360) + 0.123064559069 := by gcongr
    _ ≤ (0.160505819765 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052617570470)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367339234) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281626821501) :
    parallelOracle 12817 0.011 xi bn cd ≤ 0.161486937126 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12817 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12817 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508811079 : ℝ) ≤ plow 12817 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.212190156360 : ℝ) ≤ √(12817 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281626821501 : ℝ) / (2 * 0.560508811079 * 113.212190156360)) * 0.160505819765 +
        0.281626821501 ^ 2 / (2 * 0.560508811079 * 113.212190156360) := by gcongr
    _ ≤ (0.161486937126 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052617570470) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367339234)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281626821501) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12817 12817 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508811079 : ℝ) ≤ plow 12817 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.212190156360 : ℝ) ≤ √(12817 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12817 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12817 Θ 1.22 ≤ 0.011713407348 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.212190156360 := by gcongr <;> linarith
      _ ≤ (0.011713407348 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12817 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12817 12817 0.011 ≤ 0.008443322175 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12817 12817 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12817 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12817 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12817 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12817 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161486937126 + 0.011713407348 + (0.008443322175 : ℝ) *
        (1 + 2 * (0.281626821501 + 0.011713407348) / (0.560508811079 * 113.212190156360))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12817]

end BstLean.Part269.N12817

/-! The original eight local profiles supply actual 12817 moment certificates. -/
namespace BstLean.Part269.N12817
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12817 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12817 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12817 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052617570470 ∧
    0 ≤ bN 12817 BstLean.Part154.csC (groupTheta g) ∧ bN 12817 BstLean.Part154.csC (groupTheta g) ≤ 0.001367339234 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12817 12817 0.011
      (momentAllowance 12817 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12817 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12817 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12817 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12817 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12817 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229385201071 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12817 0.011
      (momentAllowance 12817 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12817 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12817
/-! The actual computed-centre upper energy formula at 12817. -/
namespace BstLean.Part269.N12817
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12817

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12817
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12817)
open BstLean.Part268 (cell12817)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085156186445
  | 2 => 0.086092956715
  | 3 => 0.087027020238
  | 4 => 0.087959598328
  | 5 => 0.088892174422
  | 6 => 0.089826533809
  | 7 => 0.090764807238
  | 8 => 0.091709518481
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12817 12817 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12817 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12817

/-! Actual upper energy certificates on all 43 source endpoints at 12817. -/
namespace BstLean.Part269.N12817
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12817)
open BstLean.Part268 (cell12817)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12817 (gMinus 12817) (1 - (cell12817 i).lower) ≤ 1 ∧
    energyUpper 12817 (gMinus 12817) (BstLean.Part211.gPlus 12817)
      (finiteEnergy 12817 12817 0.011) (1 - (cell12817 i).lower) ≤
      (cell12817 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨10,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨11,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨12,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨13,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨14,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨15,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨16,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨17,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨18,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨19,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨20,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨21,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨22,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨23,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨24,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨25,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨26,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨27,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨28,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨29,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨30,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨31,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨32,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨33,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨34,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨35,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨36,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨37,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨38,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨39,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨40,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨41,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨42,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨43,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨44,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨45,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨46,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨47,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨48,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨49,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨50,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨51,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12817) (by norm_num)
        (q := 1 - (cell12817 ⟨52,by decide⟩).lower)
        (by norm_num [cell12817]) (by norm_num [cell12817])
      exact ⟨E.1,E.2.trans (by norm_num [cell12817])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12817

/-! Source-cell containment and simple scalar guards at 12817. -/
namespace BstLean.Part269.N12817
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12817)
open BstLean.Part268 (cell12817)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12817 ⟨10,by decide⟩).lower ∧ (cell12817 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12817 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12817 ⟨11,by decide⟩).lower ∧ (cell12817 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12817 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12817 ⟨12,by decide⟩).lower ∧ (cell12817 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12817 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12817 ⟨13,by decide⟩).lower ∧ (cell12817 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12817 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12817 ⟨14,by decide⟩).lower ∧ (cell12817 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12817 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12817 ⟨15,by decide⟩).lower ∧ (cell12817 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12817 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12817 ⟨16,by decide⟩).lower ∧ (cell12817 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12817 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12817 ⟨17,by decide⟩).lower ∧ (cell12817 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12817 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12817 ⟨18,by decide⟩).lower ∧ (cell12817 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12817 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12817 ⟨19,by decide⟩).lower ∧ (cell12817 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12817 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12817 ⟨20,by decide⟩).lower ∧ (cell12817 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12817 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12817 ⟨21,by decide⟩).lower ∧ (cell12817 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12817 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12817 ⟨22,by decide⟩).lower ∧ (cell12817 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12817 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12817 ⟨23,by decide⟩).lower ∧ (cell12817 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12817 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12817 ⟨24,by decide⟩).lower ∧ (cell12817 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12817 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12817 ⟨25,by decide⟩).lower ∧ (cell12817 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12817 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12817 ⟨26,by decide⟩).lower ∧ (cell12817 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12817 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12817 ⟨27,by decide⟩).lower ∧ (cell12817 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12817 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12817 ⟨28,by decide⟩).lower ∧ (cell12817 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12817 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12817 ⟨29,by decide⟩).lower ∧ (cell12817 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12817 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12817 ⟨30,by decide⟩).lower ∧ (cell12817 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12817 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12817 ⟨31,by decide⟩).lower ∧ (cell12817 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12817 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12817 ⟨32,by decide⟩).lower ∧ (cell12817 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12817 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12817 ⟨33,by decide⟩).lower ∧ (cell12817 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12817 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12817 ⟨34,by decide⟩).lower ∧ (cell12817 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12817 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12817 ⟨35,by decide⟩).lower ∧ (cell12817 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12817 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12817 ⟨36,by decide⟩).lower ∧ (cell12817 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12817 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12817 ⟨37,by decide⟩).lower ∧ (cell12817 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12817 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12817 ⟨38,by decide⟩).lower ∧ (cell12817 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12817 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12817 ⟨39,by decide⟩).lower ∧ (cell12817 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12817 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12817 ⟨40,by decide⟩).lower ∧ (cell12817 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12817 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12817 ⟨41,by decide⟩).lower ∧ (cell12817 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12817 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12817 ⟨42,by decide⟩).lower ∧ (cell12817 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12817 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12817 ⟨43,by decide⟩).lower ∧ (cell12817 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12817 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12817 ⟨44,by decide⟩).lower ∧ (cell12817 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12817 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12817 ⟨45,by decide⟩).lower ∧ (cell12817 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12817 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12817 ⟨46,by decide⟩).lower ∧ (cell12817 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12817 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12817 ⟨47,by decide⟩).lower ∧ (cell12817 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12817 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12817 ⟨48,by decide⟩).lower ∧ (cell12817 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12817 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12817 ⟨49,by decide⟩).lower ∧ (cell12817 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12817 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12817 ⟨50,by decide⟩).lower ∧ (cell12817 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12817 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12817 ⟨51,by decide⟩).lower ∧ (cell12817 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12817 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12817 ⟨52,by decide⟩).lower ∧ (cell12817 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12817 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12817 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12817 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12817,cell12817,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12817 i).lower ∧
    (cell12817 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12817 i).upper ≤ (0.532 : ℝ) ∧
    (cell12817 i).centre ≤ (0.1 : ℝ) ∧ (cell12817 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12817 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12817 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12817

/-! The local source numeric instances at 12817 have no network premises. -/
namespace BstLean.Part269.N12817
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12817)
open BstLean.Part268 (cell12817)

noncomputable def sourceNumerics12817 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12817 (cell12817 i)
      scalarRow12817.M scalarRow12817.H scalarRow12817.xi := by
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
    energy_allowance := scalarRow12817.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12817]
    centre_nonneg := (scalarRow12817.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12817])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12817
/-! Actual 12818 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12818
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12818 ≤ (1.035642567189 : ℝ) := by
  have hr : (113.216606555752 : ℝ) ≤ √(12818 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.216606555752 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12818 12818 (11 / 1000) ≤
    (0.008442992811 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12818) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.216606555752 : ℝ) ≤ √(12818 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12818)
  have hdiv : K / √(12818 : ℝ) ≤ K / 113.216606555752 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.216606555752 ≤ (0.008442992811 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12818.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12818 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12818 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12818 := gPlus_lower 12818
end BstLean.Part269.N12818

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12818
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035642567188 : ℝ) ≤ wn 12818 := by
  have hn : √(12818 : ℝ) ≤ 113.216606555753 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12818 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.216606555753 ≤ 2 / √(12818 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249521950 : ℝ) ≤ rhoBar 12818 BstLean.Part154.csC ∧
    rhoBar 12818 BstLean.Part154.csC ≤ 0.000249522337 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035642567188 : ℝ) / (1.295212 * 12818) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035642567189 : ℝ) / (1.29521 * 12818) := by gcongr
      _ ≤ (0.000249522337 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12818 BstLean.Part154.csC) ≤ 0.000998151610 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12818 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12818 BstLean.Part154.csC) (piBar (rhoBar 12818 BstLean.Part154.csC)) ≤ 0.000190586761 ∧
    cc1 (rhoBar 12818 BstLean.Part154.csC) (piBar (rhoBar 12818 BstLean.Part154.csC)) ≤ 0.000121271639 ∧
    cc2 (rhoBar 12818 BstLean.Part154.csC) ≤ 0.000070399136 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12818 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12818 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12818 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12818 BstLean.Part154.csC * nuR (rhoBar 12818 BstLean.Part154.csC)) ≤ 0.000499060240 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249522337 : ℝ) * 0.000998151610 := by gcongr
      _ ≤ (0.000499060240 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12818 BstLean.Part154.csC) * nuR (rhoBar 12818 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000998151610 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12818 BstLean.Part154.csC) * rhoBar 12818 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249522337 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249522337 / 2 + 0.399 * 0.000998151610 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190586761 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499060240 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121271639 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249522337 / 1.414213562 := by gcongr
      _ ≤ (0.000070399136 : ℝ) := by norm_num

end BstLean.Part269.N12818

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12818
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12818 BstLean.Part154.csC) (piBar (rhoBar 12818 BstLean.Part154.csC)) ≤ 1.56863E-7 := by
  have hr0 : 0 ≤ rhoBar 12818 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12818 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12818 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12818 BstLean.Part154.csC) (piBar (rhoBar 12818 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12818 BstLean.Part154.csC) (piBar (rhoBar 12818 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12818 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190586761 : ℝ) ^ 2 + 0.000121271639 ^ 2 + 3 * 0.000070399136 ^ 2 +
        2 * 0.797885 * 0.000190586761 * 0.000121271639 + 2 * 0.000190586761 * 0.000070399136 +
        4 * 0.797885 * 0.000121271639 * 0.000070399136 := by gcongr
    _ ≤ (1.56863E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12818 BstLean.Part154.csC Θ ≤ 0.002604243836 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12818 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12818 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12818 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12818 BstLean.Part154.csC) (piBar (rhoBar 12818 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12818 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035642567189 * 1.56863E-7 / (0.000249521950 : ℝ) := by gcongr
    _ ≤ 0.002604243836 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12818 BstLean.Part154.csC Θ ≤ 0.002889084929 + 0.000658050960 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12818 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12818 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12818 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035642567189 : ℝ) * ((2 * Θ * 0.000249522337 +
        (6863 / 10000) * 0.000249522337 * 12818 * 0.000998151610) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002889084929 + 0.000658050960 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12818 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12818 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12818 0.011 Θ ∧ gammaRatio 12818 0.011 Θ ≤ 0.000085779327 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12818 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035642567189 : ℝ) * 0.525 / ((1 - 0.011) * 12818) := by gcongr
      _ ≤ (0.000085779327 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12818 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12818 0.011 Θ) :=
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
    badAllowance 12818 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12818 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12818 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12818 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12818 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12818 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12818 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12818 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12818 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12818 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12818 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035642567189 : ℝ) * 12818 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12818 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003397889429 + 0.003262294796 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12818

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12818
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12818 BstLean.Part154.csC) (piBar (rhoBar 12818 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12818 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12818 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12818 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12818 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12818 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12818 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12818 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12818 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12818 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12818 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12818 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12818 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12818 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12818 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052239560574 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12818) ≤ 0.010548254514 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12818 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035642567189)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010548254514 + 2 * 0.737676 / 12818) := by gcongr
    _ ≤ (0.052239560574 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12818 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12818

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12818
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508855476 : ℝ) ≤ plow 12818 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12818) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052617194197)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367228014) : eMP 12818 0.011 xi bn ≤ 0.001177211508 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12818 : ℝ) * (1 - 0.011))) ≤ 0.000582086002 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001367228014 / (12818 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582086002 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582086002 : ℝ) + 3.141593 * 0.052617194197 / (12818 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001177211508 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052617194197)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367228014) : PiBarMP 12818 12 0.011 xi bn ≤ 0.160499490230 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12818 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036976046490 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.592193335062 : ℝ) ≤ √((12818 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.216606555752 : ℝ) ≤ √(12818 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12818) ≤ 0.123059758517 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036976046490 + 0.052617194197 * 1.772454 / (2 * (112.592193335062 : ℝ))) * (1 + 0.001177211508) +
        8 / (12818 * 113.216606555752) + 0.123059758517 := by gcongr
    _ ≤ (0.160499490230 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052617194197)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367228014) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281623941466) :
    parallelOracle 12818 0.011 xi bn cd ≤ 0.161480538773 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12818 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12818 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508855476 : ℝ) ≤ plow 12818 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.216606555752 : ℝ) ≤ √(12818 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281623941466 : ℝ) / (2 * 0.560508855476 * 113.216606555752)) * 0.160499490230 +
        0.281623941466 ^ 2 / (2 * 0.560508855476 * 113.216606555752) := by gcongr
    _ ≤ (0.161480538773 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052617194197) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367228014)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281623941466) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12818 12818 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508855476 : ℝ) ≤ plow 12818 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.216606555752 : ℝ) ≤ √(12818 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12818 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12818 Θ 1.22 ≤ 0.011712950427 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.216606555752 := by gcongr <;> linarith
      _ ≤ (0.011712950427 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12818 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12818 12818 0.011 ≤ 0.008442992811 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12818 12818 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12818 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12818 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12818 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12818 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161480538773 + 0.011712950427 + (0.008442992811 : ℝ) *
        (1 + 2 * (0.281623941466 + 0.011712950427) / (0.560508855476 * 113.216606555752))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12818]

end BstLean.Part269.N12818

/-! The original eight local profiles supply actual 12818 moment certificates. -/
namespace BstLean.Part269.N12818
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12818 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12818 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12818 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052617194197 ∧
    0 ≤ bN 12818 BstLean.Part154.csC (groupTheta g) ∧ bN 12818 BstLean.Part154.csC (groupTheta g) ≤ 0.001367228014 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12818 12818 0.011
      (momentAllowance 12818 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12818 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12818 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12818 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12818 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12818 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229384380892 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12818 0.011
      (momentAllowance 12818 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12818 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12818
/-! The actual computed-centre upper energy formula at 12818. -/
namespace BstLean.Part269.N12818
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12818

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12818
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12818)
open BstLean.Part268 (cell12818)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085153390303
  | 2 => 0.086090111843
  | 3 => 0.087024119962
  | 4 => 0.087956634405
  | 5 => 0.088889136760
  | 6 => 0.089823410152
  | 7 => 0.090761582806
  | 8 => 0.091706175578
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12818 12818 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12818 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12818

/-! Actual upper energy certificates on all 43 source endpoints at 12818. -/
namespace BstLean.Part269.N12818
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12818)
open BstLean.Part268 (cell12818)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12818 (gMinus 12818) (1 - (cell12818 i).lower) ≤ 1 ∧
    energyUpper 12818 (gMinus 12818) (BstLean.Part211.gPlus 12818)
      (finiteEnergy 12818 12818 0.011) (1 - (cell12818 i).lower) ≤
      (cell12818 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨10,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨11,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨12,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨13,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨14,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨15,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨16,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨17,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨18,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨19,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨20,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨21,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨22,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨23,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨24,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨25,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨26,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨27,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨28,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨29,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨30,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨31,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨32,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨33,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨34,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨35,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨36,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨37,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨38,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨39,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨40,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨41,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨42,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨43,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨44,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨45,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨46,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨47,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨48,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨49,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨50,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨51,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12818) (by norm_num)
        (q := 1 - (cell12818 ⟨52,by decide⟩).lower)
        (by norm_num [cell12818]) (by norm_num [cell12818])
      exact ⟨E.1,E.2.trans (by norm_num [cell12818])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12818

/-! Source-cell containment and simple scalar guards at 12818. -/
namespace BstLean.Part269.N12818
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12818)
open BstLean.Part268 (cell12818)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12818 ⟨10,by decide⟩).lower ∧ (cell12818 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12818 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12818 ⟨11,by decide⟩).lower ∧ (cell12818 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12818 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12818 ⟨12,by decide⟩).lower ∧ (cell12818 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12818 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12818 ⟨13,by decide⟩).lower ∧ (cell12818 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12818 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12818 ⟨14,by decide⟩).lower ∧ (cell12818 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12818 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12818 ⟨15,by decide⟩).lower ∧ (cell12818 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12818 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12818 ⟨16,by decide⟩).lower ∧ (cell12818 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12818 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12818 ⟨17,by decide⟩).lower ∧ (cell12818 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12818 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12818 ⟨18,by decide⟩).lower ∧ (cell12818 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12818 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12818 ⟨19,by decide⟩).lower ∧ (cell12818 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12818 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12818 ⟨20,by decide⟩).lower ∧ (cell12818 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12818 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12818 ⟨21,by decide⟩).lower ∧ (cell12818 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12818 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12818 ⟨22,by decide⟩).lower ∧ (cell12818 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12818 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12818 ⟨23,by decide⟩).lower ∧ (cell12818 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12818 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12818 ⟨24,by decide⟩).lower ∧ (cell12818 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12818 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12818 ⟨25,by decide⟩).lower ∧ (cell12818 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12818 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12818 ⟨26,by decide⟩).lower ∧ (cell12818 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12818 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12818 ⟨27,by decide⟩).lower ∧ (cell12818 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12818 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12818 ⟨28,by decide⟩).lower ∧ (cell12818 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12818 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12818 ⟨29,by decide⟩).lower ∧ (cell12818 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12818 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12818 ⟨30,by decide⟩).lower ∧ (cell12818 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12818 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12818 ⟨31,by decide⟩).lower ∧ (cell12818 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12818 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12818 ⟨32,by decide⟩).lower ∧ (cell12818 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12818 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12818 ⟨33,by decide⟩).lower ∧ (cell12818 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12818 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12818 ⟨34,by decide⟩).lower ∧ (cell12818 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12818 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12818 ⟨35,by decide⟩).lower ∧ (cell12818 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12818 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12818 ⟨36,by decide⟩).lower ∧ (cell12818 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12818 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12818 ⟨37,by decide⟩).lower ∧ (cell12818 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12818 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12818 ⟨38,by decide⟩).lower ∧ (cell12818 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12818 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12818 ⟨39,by decide⟩).lower ∧ (cell12818 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12818 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12818 ⟨40,by decide⟩).lower ∧ (cell12818 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12818 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12818 ⟨41,by decide⟩).lower ∧ (cell12818 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12818 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12818 ⟨42,by decide⟩).lower ∧ (cell12818 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12818 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12818 ⟨43,by decide⟩).lower ∧ (cell12818 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12818 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12818 ⟨44,by decide⟩).lower ∧ (cell12818 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12818 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12818 ⟨45,by decide⟩).lower ∧ (cell12818 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12818 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12818 ⟨46,by decide⟩).lower ∧ (cell12818 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12818 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12818 ⟨47,by decide⟩).lower ∧ (cell12818 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12818 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12818 ⟨48,by decide⟩).lower ∧ (cell12818 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12818 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12818 ⟨49,by decide⟩).lower ∧ (cell12818 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12818 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12818 ⟨50,by decide⟩).lower ∧ (cell12818 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12818 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12818 ⟨51,by decide⟩).lower ∧ (cell12818 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12818 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12818 ⟨52,by decide⟩).lower ∧ (cell12818 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12818 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12818 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12818 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12818,cell12818,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12818 i).lower ∧
    (cell12818 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12818 i).upper ≤ (0.532 : ℝ) ∧
    (cell12818 i).centre ≤ (0.1 : ℝ) ∧ (cell12818 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12818 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12818 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12818

/-! The local source numeric instances at 12818 have no network premises. -/
namespace BstLean.Part269.N12818
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12818)
open BstLean.Part268 (cell12818)

noncomputable def sourceNumerics12818 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12818 (cell12818 i)
      scalarRow12818.M scalarRow12818.H scalarRow12818.xi := by
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
    energy_allowance := scalarRow12818.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12818]
    centre_nonneg := (scalarRow12818.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12818])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12818
/-! Actual 12819 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12819
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12819 ≤ (1.035641164766 : ℝ) := by
  have hr : (113.221022782873 : ℝ) ≤ √(12819 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.221022782873 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12819 12819 (11 / 1000) ≤
    (0.008442663487 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12819) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.221022782873 : ℝ) ≤ √(12819 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12819)
  have hdiv : K / √(12819 : ℝ) ≤ K / 113.221022782873 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.221022782873 ≤ (0.008442663487 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12819.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12819 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12819 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12819 := gPlus_lower 12819
end BstLean.Part269.N12819

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12819
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035641164765 : ℝ) ≤ wn 12819 := by
  have hn : √(12819 : ℝ) ≤ 113.221022782874 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12819 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.221022782874 ≤ 2 / √(12819 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249502147 : ℝ) ≤ rhoBar 12819 BstLean.Part154.csC ∧
    rhoBar 12819 BstLean.Part154.csC ≤ 0.000249502534 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035641164765 : ℝ) / (1.295212 * 12819) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035641164766 : ℝ) / (1.29521 * 12819) := by gcongr
      _ ≤ (0.000249502534 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12819 BstLean.Part154.csC) ≤ 0.000998072388 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12819 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12819 BstLean.Part154.csC) (piBar (rhoBar 12819 BstLean.Part154.csC)) ≤ 0.000190571635 ∧
    cc1 (rhoBar 12819 BstLean.Part154.csC) (piBar (rhoBar 12819 BstLean.Part154.csC)) ≤ 0.000121262014 ∧
    cc2 (rhoBar 12819 BstLean.Part154.csC) ≤ 0.000070393549 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12819 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12819 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12819 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12819 BstLean.Part154.csC * nuR (rhoBar 12819 BstLean.Part154.csC)) ≤ 0.000499020631 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249502534 : ℝ) * 0.000998072388 := by gcongr
      _ ≤ (0.000499020631 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12819 BstLean.Part154.csC) * nuR (rhoBar 12819 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000998072388 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12819 BstLean.Part154.csC) * rhoBar 12819 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249502534 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249502534 / 2 + 0.399 * 0.000998072388 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190571635 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000499020631 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121262014 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249502534 / 1.414213562 := by gcongr
      _ ≤ (0.000070393549 : ℝ) := by norm_num

end BstLean.Part269.N12819

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12819
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12819 BstLean.Part154.csC) (piBar (rhoBar 12819 BstLean.Part154.csC)) ≤ 1.56838E-7 := by
  have hr0 : 0 ≤ rhoBar 12819 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12819 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12819 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12819 BstLean.Part154.csC) (piBar (rhoBar 12819 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12819 BstLean.Part154.csC) (piBar (rhoBar 12819 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12819 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190571635 : ℝ) ^ 2 + 0.000121262014 ^ 2 + 3 * 0.000070393549 ^ 2 +
        2 * 0.797885 * 0.000190571635 * 0.000121262014 + 2 * 0.000190571635 * 0.000070393549 +
        4 * 0.797885 * 0.000121262014 * 0.000070393549 := by gcongr
    _ ≤ (1.56838E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12819 BstLean.Part154.csC Θ ≤ 0.002604031925 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12819 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12819 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12819 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12819 BstLean.Part154.csC) (piBar (rhoBar 12819 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12819 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035641164766 * 1.56838E-7 / (0.000249502147 : ℝ) := by gcongr
    _ ≤ 0.002604031925 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12819 BstLean.Part154.csC Θ ≤ 0.002888847801 + 0.000657997843 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12819 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12819 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12819 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035641164766 : ℝ) * ((2 * Θ * 0.000249502534 +
        (6863 / 10000) * 0.000249502534 * 12819 * 0.000998072388) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002888847801 + 0.000657997843 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12819 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12819 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12819 0.011 Θ ∧ gammaRatio 12819 0.011 Θ ≤ 0.000085772519 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12819 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035641164766 : ℝ) * 0.525 / ((1 - 0.011) * 12819) := by gcongr
      _ ≤ (0.000085772519 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12819 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12819 0.011 Θ) :=
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
    badAllowance 12819 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12819 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12819 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12819 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12819 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12819 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12819 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12819 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12819 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12819 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12819 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035641164766 : ℝ) * 12819 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12819 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003397652301 + 0.003262029768 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12819

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12819
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12819 BstLean.Part154.csC) (piBar (rhoBar 12819 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12819 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12819 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12819 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12819 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12819 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12819 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12819 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12819 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12819 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12819 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12819 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12819 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12819 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12819 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052237500955 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12819) ≤ 0.010547843075 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12819 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035641164766)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010547843075 + 2 * 0.737676 / 12819) := by gcongr
    _ ≤ (0.052237500955 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12819 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12819

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12819
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508899867 : ℝ) ≤ plow 12819 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12819) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052616817930)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367116761) : eMP 12819 0.011 xi bn ≤ 0.001177117623 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12819 : ℝ) * (1 - 0.011))) ≤ 0.000582039615 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001367116761 / (12819 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000582039615 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000582039615 : ℝ) + 3.141593 * 0.052616817930 / (12819 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001177117623 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052616817930)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367116761) : PiBarMP 12819 12 0.011 xi bn ≤ 0.160493160752 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12819 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036974542067 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.596585205769 : ℝ) ≤ √((12819 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.221022782873 : ℝ) ≤ √(12819 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12819) ≤ 0.123054958526 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036974542067 + 0.052616817930 * 1.772454 / (2 * (112.596585205769 : ℝ))) * (1 + 0.001177117623) +
        8 / (12819 * 113.221022782873) + 0.123054958526 := by gcongr
    _ ≤ (0.160493160752 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052616817930)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367116761) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281621061679) :
    parallelOracle 12819 0.011 xi bn cd ≤ 0.161474140486 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12819 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12819 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508899867 : ℝ) ≤ plow 12819 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.221022782873 : ℝ) ≤ √(12819 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281621061679 : ℝ) / (2 * 0.560508899867 * 113.221022782873)) * 0.160493160752 +
        0.281621061679 ^ 2 / (2 * 0.560508899867 * 113.221022782873) := by gcongr
    _ ≤ (0.161474140486 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052616817930) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367116761)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281621061679) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12819 12819 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508899867 : ℝ) ≤ plow 12819 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.221022782873 : ℝ) ≤ √(12819 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12819 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12819 Θ 1.22 ≤ 0.011712493559 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.221022782873 := by gcongr <;> linarith
      _ ≤ (0.011712493559 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12819 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12819 12819 0.011 ≤ 0.008442663487 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12819 12819 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12819 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12819 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12819 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12819 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161474140486 + 0.011712493559 + (0.008442663487 : ℝ) *
        (1 + 2 * (0.281621061679 + 0.011712493559) / (0.560508899867 * 113.221022782873))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12819]

end BstLean.Part269.N12819

/-! The original eight local profiles supply actual 12819 moment certificates. -/
namespace BstLean.Part269.N12819
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12819 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12819 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12819 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052616817930 ∧
    0 ≤ bN 12819 BstLean.Part154.csC (groupTheta g) ∧ bN 12819 BstLean.Part154.csC (groupTheta g) ≤ 0.001367116761 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12819 12819 0.011
      (momentAllowance 12819 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12819 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12819 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12819 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12819 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12819 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229383560724 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12819 0.011
      (momentAllowance 12819 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12819 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12819
/-! The actual computed-centre upper energy formula at 12819. -/
namespace BstLean.Part269.N12819
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12819

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12819
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12819)
open BstLean.Part268 (cell12819)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085150595125
  | 2 => 0.086087267974
  | 3 => 0.087021220735
  | 4 => 0.087953671589
  | 5 => 0.088886100277
  | 6 => 0.089820287759
  | 7 => 0.090758359744
  | 8 => 0.091702834170
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12819 12819 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12819 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12819

/-! Actual upper energy certificates on all 43 source endpoints at 12819. -/
namespace BstLean.Part269.N12819
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12819)
open BstLean.Part268 (cell12819)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12819 (gMinus 12819) (1 - (cell12819 i).lower) ≤ 1 ∧
    energyUpper 12819 (gMinus 12819) (BstLean.Part211.gPlus 12819)
      (finiteEnergy 12819 12819 0.011) (1 - (cell12819 i).lower) ≤
      (cell12819 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨10,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨11,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨12,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨13,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨14,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨15,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨16,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨17,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨18,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨19,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨20,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨21,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨22,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨23,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨24,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨25,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨26,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨27,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨28,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨29,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨30,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨31,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨32,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨33,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨34,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨35,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨36,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨37,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨38,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨39,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨40,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨41,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨42,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨43,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨44,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨45,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨46,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨47,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨48,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨49,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨50,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨51,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12819) (by norm_num)
        (q := 1 - (cell12819 ⟨52,by decide⟩).lower)
        (by norm_num [cell12819]) (by norm_num [cell12819])
      exact ⟨E.1,E.2.trans (by norm_num [cell12819])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12819

/-! Source-cell containment and simple scalar guards at 12819. -/
namespace BstLean.Part269.N12819
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12819)
open BstLean.Part268 (cell12819)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12819 ⟨10,by decide⟩).lower ∧ (cell12819 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12819 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12819 ⟨11,by decide⟩).lower ∧ (cell12819 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12819 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12819 ⟨12,by decide⟩).lower ∧ (cell12819 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12819 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12819 ⟨13,by decide⟩).lower ∧ (cell12819 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12819 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12819 ⟨14,by decide⟩).lower ∧ (cell12819 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12819 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12819 ⟨15,by decide⟩).lower ∧ (cell12819 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12819 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12819 ⟨16,by decide⟩).lower ∧ (cell12819 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12819 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12819 ⟨17,by decide⟩).lower ∧ (cell12819 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12819 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12819 ⟨18,by decide⟩).lower ∧ (cell12819 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12819 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12819 ⟨19,by decide⟩).lower ∧ (cell12819 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12819 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12819 ⟨20,by decide⟩).lower ∧ (cell12819 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12819 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12819 ⟨21,by decide⟩).lower ∧ (cell12819 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12819 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12819 ⟨22,by decide⟩).lower ∧ (cell12819 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12819 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12819 ⟨23,by decide⟩).lower ∧ (cell12819 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12819 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12819 ⟨24,by decide⟩).lower ∧ (cell12819 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12819 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12819 ⟨25,by decide⟩).lower ∧ (cell12819 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12819 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12819 ⟨26,by decide⟩).lower ∧ (cell12819 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12819 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12819 ⟨27,by decide⟩).lower ∧ (cell12819 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12819 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12819 ⟨28,by decide⟩).lower ∧ (cell12819 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12819 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12819 ⟨29,by decide⟩).lower ∧ (cell12819 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12819 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12819 ⟨30,by decide⟩).lower ∧ (cell12819 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12819 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12819 ⟨31,by decide⟩).lower ∧ (cell12819 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12819 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12819 ⟨32,by decide⟩).lower ∧ (cell12819 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12819 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12819 ⟨33,by decide⟩).lower ∧ (cell12819 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12819 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12819 ⟨34,by decide⟩).lower ∧ (cell12819 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12819 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12819 ⟨35,by decide⟩).lower ∧ (cell12819 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12819 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12819 ⟨36,by decide⟩).lower ∧ (cell12819 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12819 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12819 ⟨37,by decide⟩).lower ∧ (cell12819 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12819 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12819 ⟨38,by decide⟩).lower ∧ (cell12819 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12819 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12819 ⟨39,by decide⟩).lower ∧ (cell12819 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12819 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12819 ⟨40,by decide⟩).lower ∧ (cell12819 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12819 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12819 ⟨41,by decide⟩).lower ∧ (cell12819 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12819 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12819 ⟨42,by decide⟩).lower ∧ (cell12819 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12819 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12819 ⟨43,by decide⟩).lower ∧ (cell12819 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12819 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12819 ⟨44,by decide⟩).lower ∧ (cell12819 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12819 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12819 ⟨45,by decide⟩).lower ∧ (cell12819 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12819 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12819 ⟨46,by decide⟩).lower ∧ (cell12819 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12819 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12819 ⟨47,by decide⟩).lower ∧ (cell12819 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12819 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12819 ⟨48,by decide⟩).lower ∧ (cell12819 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12819 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12819 ⟨49,by decide⟩).lower ∧ (cell12819 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12819 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12819 ⟨50,by decide⟩).lower ∧ (cell12819 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12819 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12819 ⟨51,by decide⟩).lower ∧ (cell12819 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12819 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12819 ⟨52,by decide⟩).lower ∧ (cell12819 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12819 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12819 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12819 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12819,cell12819,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12819 i).lower ∧
    (cell12819 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12819 i).upper ≤ (0.532 : ℝ) ∧
    (cell12819 i).centre ≤ (0.1 : ℝ) ∧ (cell12819 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12819 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12819 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12819

/-! The local source numeric instances at 12819 have no network premises. -/
namespace BstLean.Part269.N12819
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12819)
open BstLean.Part268 (cell12819)

noncomputable def sourceNumerics12819 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12819 (cell12819 i)
      scalarRow12819.M scalarRow12819.H scalarRow12819.xi := by
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
    energy_allowance := scalarRow12819.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12819]
    centre_nonneg := (scalarRow12819.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12819])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12819
/-! Actual 12820 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12820
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12820 ≤ (1.035639762508 : ℝ) := by
  have hr : (113.225438837745 : ℝ) ≤ √(12820 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.225438837745 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12820 12820 (11 / 1000) ≤
    (0.008442334201 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12820) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.225438837745 : ℝ) ≤ √(12820 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12820)
  have hdiv : K / √(12820 : ℝ) ≤ K / 113.225438837745 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.225438837745 ≤ (0.008442334201 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12820.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12820 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12820 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12820 := gPlus_lower 12820
end BstLean.Part269.N12820

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12820
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035639762507 : ℝ) ≤ wn 12820 := by
  have hn : √(12820 : ℝ) ≤ 113.225438837746 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12820 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.225438837746 ≤ 2 / √(12820 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249482348 : ℝ) ≤ rhoBar 12820 BstLean.Part154.csC ∧
    rhoBar 12820 BstLean.Part154.csC ≤ 0.000249482734 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035639762507 : ℝ) / (1.295212 * 12820) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035639762508 : ℝ) / (1.29521 * 12820) := by gcongr
      _ ≤ (0.000249482734 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12820 BstLean.Part154.csC) ≤ 0.000997993178 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12820 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12820 BstLean.Part154.csC) (piBar (rhoBar 12820 BstLean.Part154.csC)) ≤ 0.000190556511 ∧
    cc1 (rhoBar 12820 BstLean.Part154.csC) (piBar (rhoBar 12820 BstLean.Part154.csC)) ≤ 0.000121252391 ∧
    cc2 (rhoBar 12820 BstLean.Part154.csC) ≤ 0.000070387963 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12820 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12820 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12820 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12820 BstLean.Part154.csC * nuR (rhoBar 12820 BstLean.Part154.csC)) ≤ 0.000498981029 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249482734 : ℝ) * 0.000997993178 := by gcongr
      _ ≤ (0.000498981029 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12820 BstLean.Part154.csC) * nuR (rhoBar 12820 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000997993178 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12820 BstLean.Part154.csC) * rhoBar 12820 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249482734 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249482734 / 2 + 0.399 * 0.000997993178 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190556511 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498981029 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121252391 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249482734 / 1.414213562 := by gcongr
      _ ≤ (0.000070387963 : ℝ) := by norm_num

end BstLean.Part269.N12820

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12820
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12820 BstLean.Part154.csC) (piBar (rhoBar 12820 BstLean.Part154.csC)) ≤ 1.56813E-7 := by
  have hr0 : 0 ≤ rhoBar 12820 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12820 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12820 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12820 BstLean.Part154.csC) (piBar (rhoBar 12820 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12820 BstLean.Part154.csC) (piBar (rhoBar 12820 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12820 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190556511 : ℝ) ^ 2 + 0.000121252391 ^ 2 + 3 * 0.000070387963 ^ 2 +
        2 * 0.797885 * 0.000190556511 * 0.000121252391 + 2 * 0.000190556511 * 0.000070387963 +
        4 * 0.797885 * 0.000121252391 * 0.000070387963 := by gcongr
    _ ≤ (1.56813E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12820 BstLean.Part154.csC Θ ≤ 0.002603819940 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12820 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12820 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12820 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12820 BstLean.Part154.csC) (piBar (rhoBar 12820 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12820 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035639762508 * 1.56813E-7 / (0.000249482348 : ℝ) := by gcongr
    _ ≤ 0.002603819940 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12820 BstLean.Part154.csC Θ ≤ 0.002888610708 + 0.000657944735 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12820 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12820 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12820 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035639762508 : ℝ) * ((2 * Θ * 0.000249482734 +
        (6863 / 10000) * 0.000249482734 * 12820 * 0.000997993178) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002888610708 + 0.000657944735 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12820 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12820 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12820 0.011 Θ ∧ gammaRatio 12820 0.011 Θ ≤ 0.000085765713 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12820 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035639762508 : ℝ) * 0.525 / ((1 - 0.011) * 12820) := by gcongr
      _ ≤ (0.000085765713 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12820 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12820 0.011 Θ) :=
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
    badAllowance 12820 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12820 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12820 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12820 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12820 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12820 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12820 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12820 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12820 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12820 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12820 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035639762508 : ℝ) * 12820 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12820 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003397415208 + 0.003261764675 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12820

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12820
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12820 BstLean.Part154.csC) (piBar (rhoBar 12820 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12820 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12820 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12820 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12820 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12820 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12820 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12820 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12820 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12820 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12820 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12820 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12820 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12820 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12820 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052235441583 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12820) ≤ 0.010547431685 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12820 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035639762508)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010547431685 + 2 * 0.737676 / 12820) := by gcongr
    _ ≤ (0.052235441583 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12820 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12820

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12820
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508944251 : ℝ) ≤ plow 12820 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12820) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052616441663)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367005469) : eMP 12820 0.011 xi bn ≤ 0.001177023731 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12820 : ℝ) * (1 - 0.011))) ≤ 0.000581993224 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001367005469 / (12820 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581993224 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581993224 : ℝ) + 3.141593 * 0.052616441663 / (12820 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001177023731 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052616441663)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367005469) : PiBarMP 12820 12 0.011 xi bn ≤ 0.160486831248 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12820 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036973037055 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.600976905176 : ℝ) ≤ √((12820 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.225438837745 : ℝ) ≤ √(12820 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12820) ≤ 0.123050159097 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036973037055 + 0.052616441663 * 1.772454 / (2 * (112.600976905176 : ℝ))) * (1 + 0.001177023731) +
        8 / (12820 * 113.225438837745) + 0.123050159097 := by gcongr
    _ ≤ (0.160486831248 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052616441663)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367005469) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281618182135) :
    parallelOracle 12820 0.011 xi bn cd ≤ 0.161467742181 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12820 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12820 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508944251 : ℝ) ≤ plow 12820 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.225438837745 : ℝ) ≤ √(12820 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281618182135 : ℝ) / (2 * 0.560508944251 * 113.225438837745)) * 0.160486831248 +
        0.281618182135 ^ 2 / (2 * 0.560508944251 * 113.225438837745) := by gcongr
    _ ≤ (0.161467742181 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052616441663) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001367005469)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281618182135) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12820 12820 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508944251 : ℝ) ≤ plow 12820 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.225438837745 : ℝ) ≤ √(12820 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12820 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12820 Θ 1.22 ≤ 0.011712036744 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.225438837745 := by gcongr <;> linarith
      _ ≤ (0.011712036744 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12820 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12820 12820 0.011 ≤ 0.008442334201 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12820 12820 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12820 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12820 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12820 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12820 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161467742181 + 0.011712036744 + (0.008442334201 : ℝ) *
        (1 + 2 * (0.281618182135 + 0.011712036744) / (0.560508944251 * 113.225438837745))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12820]

end BstLean.Part269.N12820

/-! The original eight local profiles supply actual 12820 moment certificates. -/
namespace BstLean.Part269.N12820
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12820 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12820 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12820 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052616441663 ∧
    0 ≤ bN 12820 BstLean.Part154.csC (groupTheta g) ∧ bN 12820 BstLean.Part154.csC (groupTheta g) ≤ 0.001367005469 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12820 12820 0.011
      (momentAllowance 12820 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12820 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12820 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12820 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12820 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12820 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229382740552 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12820 0.011
      (momentAllowance 12820 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12820 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12820
/-! The actual computed-centre upper energy formula at 12820. -/
namespace BstLean.Part269.N12820
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12820

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12820
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12820)
open BstLean.Part268 (cell12820)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085147800909
  | 2 => 0.086084425106
  | 3 => 0.087018322557
  | 4 => 0.087950709879
  | 5 => 0.088883064970
  | 6 => 0.089817166630
  | 7 => 0.090755138050
  | 8 => 0.091699494257
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12820 12820 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12820 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12820

/-! Actual upper energy certificates on all 43 source endpoints at 12820. -/
namespace BstLean.Part269.N12820
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12820)
open BstLean.Part268 (cell12820)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12820 (gMinus 12820) (1 - (cell12820 i).lower) ≤ 1 ∧
    energyUpper 12820 (gMinus 12820) (BstLean.Part211.gPlus 12820)
      (finiteEnergy 12820 12820 0.011) (1 - (cell12820 i).lower) ≤
      (cell12820 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨10,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨11,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨12,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨13,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨14,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨15,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨16,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨17,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨18,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨19,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨20,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨21,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨22,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨23,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨24,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨25,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨26,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨27,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨28,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨29,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨30,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨31,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨32,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨33,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨34,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨35,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨36,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨37,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨38,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨39,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨40,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨41,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨42,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨43,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨44,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨45,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨46,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨47,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨48,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨49,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨50,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨51,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12820) (by norm_num)
        (q := 1 - (cell12820 ⟨52,by decide⟩).lower)
        (by norm_num [cell12820]) (by norm_num [cell12820])
      exact ⟨E.1,E.2.trans (by norm_num [cell12820])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12820

/-! Source-cell containment and simple scalar guards at 12820. -/
namespace BstLean.Part269.N12820
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12820)
open BstLean.Part268 (cell12820)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12820 ⟨10,by decide⟩).lower ∧ (cell12820 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12820 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12820 ⟨11,by decide⟩).lower ∧ (cell12820 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12820 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12820 ⟨12,by decide⟩).lower ∧ (cell12820 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12820 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12820 ⟨13,by decide⟩).lower ∧ (cell12820 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12820 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12820 ⟨14,by decide⟩).lower ∧ (cell12820 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12820 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12820 ⟨15,by decide⟩).lower ∧ (cell12820 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12820 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12820 ⟨16,by decide⟩).lower ∧ (cell12820 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12820 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12820 ⟨17,by decide⟩).lower ∧ (cell12820 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12820 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12820 ⟨18,by decide⟩).lower ∧ (cell12820 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12820 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12820 ⟨19,by decide⟩).lower ∧ (cell12820 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12820 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12820 ⟨20,by decide⟩).lower ∧ (cell12820 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12820 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12820 ⟨21,by decide⟩).lower ∧ (cell12820 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12820 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12820 ⟨22,by decide⟩).lower ∧ (cell12820 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12820 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12820 ⟨23,by decide⟩).lower ∧ (cell12820 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12820 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12820 ⟨24,by decide⟩).lower ∧ (cell12820 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12820 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12820 ⟨25,by decide⟩).lower ∧ (cell12820 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12820 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12820 ⟨26,by decide⟩).lower ∧ (cell12820 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12820 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12820 ⟨27,by decide⟩).lower ∧ (cell12820 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12820 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12820 ⟨28,by decide⟩).lower ∧ (cell12820 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12820 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12820 ⟨29,by decide⟩).lower ∧ (cell12820 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12820 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12820 ⟨30,by decide⟩).lower ∧ (cell12820 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12820 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12820 ⟨31,by decide⟩).lower ∧ (cell12820 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12820 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12820 ⟨32,by decide⟩).lower ∧ (cell12820 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12820 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12820 ⟨33,by decide⟩).lower ∧ (cell12820 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12820 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12820 ⟨34,by decide⟩).lower ∧ (cell12820 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12820 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12820 ⟨35,by decide⟩).lower ∧ (cell12820 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12820 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12820 ⟨36,by decide⟩).lower ∧ (cell12820 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12820 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12820 ⟨37,by decide⟩).lower ∧ (cell12820 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12820 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12820 ⟨38,by decide⟩).lower ∧ (cell12820 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12820 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12820 ⟨39,by decide⟩).lower ∧ (cell12820 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12820 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12820 ⟨40,by decide⟩).lower ∧ (cell12820 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12820 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12820 ⟨41,by decide⟩).lower ∧ (cell12820 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12820 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12820 ⟨42,by decide⟩).lower ∧ (cell12820 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12820 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12820 ⟨43,by decide⟩).lower ∧ (cell12820 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12820 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12820 ⟨44,by decide⟩).lower ∧ (cell12820 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12820 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12820 ⟨45,by decide⟩).lower ∧ (cell12820 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12820 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12820 ⟨46,by decide⟩).lower ∧ (cell12820 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12820 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12820 ⟨47,by decide⟩).lower ∧ (cell12820 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12820 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12820 ⟨48,by decide⟩).lower ∧ (cell12820 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12820 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12820 ⟨49,by decide⟩).lower ∧ (cell12820 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12820 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12820 ⟨50,by decide⟩).lower ∧ (cell12820 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12820 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12820 ⟨51,by decide⟩).lower ∧ (cell12820 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12820 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12820 ⟨52,by decide⟩).lower ∧ (cell12820 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12820 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12820 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12820 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12820,cell12820,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12820 i).lower ∧
    (cell12820 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12820 i).upper ≤ (0.532 : ℝ) ∧
    (cell12820 i).centre ≤ (0.1 : ℝ) ∧ (cell12820 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12820 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12820 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12820

/-! The local source numeric instances at 12820 have no network premises. -/
namespace BstLean.Part269.N12820
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12820)
open BstLean.Part268 (cell12820)

noncomputable def sourceNumerics12820 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12820 (cell12820 i)
      scalarRow12820.M scalarRow12820.H scalarRow12820.xi := by
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
    energy_allowance := scalarRow12820.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12820]
    centre_nonneg := (scalarRow12820.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12820])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12820
/-! Actual 12821 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12821
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12821 ≤ (1.035638360416 : ℝ) := by
  have hr : (113.229854720387 : ℝ) ≤ √(12821 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.229854720387 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12821 12821 (11 / 1000) ≤
    (0.008442004954 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12821) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.229854720387 : ℝ) ≤ √(12821 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12821)
  have hdiv : K / √(12821 : ℝ) ≤ K / 113.229854720387 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.229854720387 ≤ (0.008442004954 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12821.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12821 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12821 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12821 := gPlus_lower 12821
end BstLean.Part269.N12821

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12821
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035638360415 : ℝ) ≤ wn 12821 := by
  have hn : √(12821 : ℝ) ≤ 113.229854720388 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12821 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.229854720388 ≤ 2 / √(12821 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249462551 : ℝ) ≤ rhoBar 12821 BstLean.Part154.csC ∧
    rhoBar 12821 BstLean.Part154.csC ≤ 0.000249462937 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035638360415 : ℝ) / (1.295212 * 12821) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035638360416 : ℝ) / (1.29521 * 12821) := by gcongr
      _ ≤ (0.000249462937 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12821 BstLean.Part154.csC) ≤ 0.000997913980 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12821 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12821 BstLean.Part154.csC) (piBar (rhoBar 12821 BstLean.Part154.csC)) ≤ 0.000190541389 ∧
    cc1 (rhoBar 12821 BstLean.Part154.csC) (piBar (rhoBar 12821 BstLean.Part154.csC)) ≤ 0.000121242768 ∧
    cc2 (rhoBar 12821 BstLean.Part154.csC) ≤ 0.000070382377 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12821 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12821 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12821 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12821 BstLean.Part154.csC * nuR (rhoBar 12821 BstLean.Part154.csC)) ≤ 0.000498941432 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249462937 : ℝ) * 0.000997913980 := by gcongr
      _ ≤ (0.000498941432 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12821 BstLean.Part154.csC) * nuR (rhoBar 12821 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000997913980 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12821 BstLean.Part154.csC) * rhoBar 12821 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249462937 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249462937 / 2 + 0.399 * 0.000997913980 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190541389 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498941432 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121242768 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249462937 / 1.414213562 := by gcongr
      _ ≤ (0.000070382377 : ℝ) := by norm_num

end BstLean.Part269.N12821

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12821
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12821 BstLean.Part154.csC) (piBar (rhoBar 12821 BstLean.Part154.csC)) ≤ 1.56789E-7 := by
  have hr0 : 0 ≤ rhoBar 12821 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12821 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12821 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12821 BstLean.Part154.csC) (piBar (rhoBar 12821 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12821 BstLean.Part154.csC) (piBar (rhoBar 12821 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12821 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190541389 : ℝ) ^ 2 + 0.000121242768 ^ 2 + 3 * 0.000070382377 ^ 2 +
        2 * 0.797885 * 0.000190541389 * 0.000121242768 + 2 * 0.000190541389 * 0.000070382377 +
        4 * 0.797885 * 0.000121242768 * 0.000070382377 := by gcongr
    _ ≤ (1.56789E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12821 BstLean.Part154.csC Θ ≤ 0.002603624508 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12821 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12821 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12821 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12821 BstLean.Part154.csC) (piBar (rhoBar 12821 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12821 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035638360416 * 1.56789E-7 / (0.000249462551 : ℝ) := by gcongr
    _ ≤ 0.002603624508 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12821 BstLean.Part154.csC Θ ≤ 0.002888373651 + 0.000657891635 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12821 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12821 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12821 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035638360416 : ℝ) * ((2 * Θ * 0.000249462937 +
        (6863 / 10000) * 0.000249462937 * 12821 * 0.000997913980) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002888373651 + 0.000657891635 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12821 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12821 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12821 0.011 Θ ∧ gammaRatio 12821 0.011 Θ ≤ 0.000085758907 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12821 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035638360416 : ℝ) * 0.525 / ((1 - 0.011) * 12821) := by gcongr
      _ ≤ (0.000085758907 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12821 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12821 0.011 Θ) :=
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
    badAllowance 12821 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12821 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12821 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12821 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12821 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12821 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12821 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12821 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12821 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12821 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12821 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035638360416 : ℝ) * 12821 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12821 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003397178151 + 0.003261516143 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12821

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12821
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12821 BstLean.Part154.csC) (piBar (rhoBar 12821 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12821 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12821 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12821 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12821 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12821 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12821 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12821 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12821 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12821 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12821 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12821 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12821 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12821 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12821 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052233382449 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12821) ≤ 0.010547020342 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12821 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035638360416)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010547020342 + 2 * 0.737676 / 12821) := by gcongr
    _ ≤ (0.052233382449 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12821 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12821

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12821
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560508988628 : ℝ) ≤ plow 12821 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12821) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052616074127)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366902867) : eMP 12821 0.011 xi bn ≤ 0.001176933547 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12821 : ℝ) * (1 - 0.011))) ≤ 0.000581948686 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001366902867 / (12821 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581948686 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581948686 : ℝ) + 3.141593 * 0.052616074127 / (12821 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001176933547 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052616074127)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366902867) : PiBarMP 12821 12 0.011 xi bn ≤ 0.160480620115 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12821 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036971649504 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.605368433303 : ℝ) ≤ √((12821 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.229854720387 : ℝ) ≤ √(12821 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12821) ≤ 0.123045360230 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036971649504 + 0.052616074127 * 1.772454 / (2 * (112.605368433303 : ℝ))) * (1 + 0.001176933547) +
        8 / (12821 * 113.229854720387) + 0.123045360230 := by gcongr
    _ ≤ (0.160480620115 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052616074127)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366902867) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281615321858) :
    parallelOracle 12821 0.011 xi bn cd ≤ 0.161461462628 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12821 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12821 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560508988628 : ℝ) ≤ plow 12821 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.229854720387 : ℝ) ≤ √(12821 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281615321858 : ℝ) / (2 * 0.560508988628 * 113.229854720387)) * 0.160480620115 +
        0.281615321858 ^ 2 / (2 * 0.560508988628 * 113.229854720387) := by gcongr
    _ ≤ (0.161461462628 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052616074127) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366902867)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281615321858) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12821 12821 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560508988628 : ℝ) ≤ plow 12821 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.229854720387 : ℝ) ≤ √(12821 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12821 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12821 Θ 1.22 ≤ 0.011711579983 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.229854720387 := by gcongr <;> linarith
      _ ≤ (0.011711579983 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12821 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12821 12821 0.011 ≤ 0.008442004954 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12821 12821 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12821 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12821 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12821 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12821 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161461462628 + 0.011711579983 + (0.008442004954 : ℝ) *
        (1 + 2 * (0.281615321858 + 0.011711579983) / (0.560508988628 * 113.229854720387))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12821]

end BstLean.Part269.N12821

/-! The original eight local profiles supply actual 12821 moment certificates. -/
namespace BstLean.Part269.N12821
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12821 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12821 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12821 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052616074127 ∧
    0 ≤ bN 12821 BstLean.Part154.csC (groupTheta g) ∧ bN 12821 BstLean.Part154.csC (groupTheta g) ≤ 0.001366902867 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12821 12821 0.011
      (momentAllowance 12821 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12821 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12821 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12821 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12821 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12821 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229381939409 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12821 0.011
      (momentAllowance 12821 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12821 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12821
/-! The actual computed-centre upper energy formula at 12821. -/
namespace BstLean.Part269.N12821
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12821

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12821
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12821)
open BstLean.Part268 (cell12821)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085145007656
  | 2 => 0.086081583238
  | 3 => 0.087015425425
  | 4 => 0.087947749273
  | 5 => 0.088880030840
  | 6 => 0.089814046763
  | 7 => 0.090751917722
  | 8 => 0.091696155836
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12821 12821 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12821 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12821

/-! Actual upper energy certificates on all 43 source endpoints at 12821. -/
namespace BstLean.Part269.N12821
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12821)
open BstLean.Part268 (cell12821)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12821 (gMinus 12821) (1 - (cell12821 i).lower) ≤ 1 ∧
    energyUpper 12821 (gMinus 12821) (BstLean.Part211.gPlus 12821)
      (finiteEnergy 12821 12821 0.011) (1 - (cell12821 i).lower) ≤
      (cell12821 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨10,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨11,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨12,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨13,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨14,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨15,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨16,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨17,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨18,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨19,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨20,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨21,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨22,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨23,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨24,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨25,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨26,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨27,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨28,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨29,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨30,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨31,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨32,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨33,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨34,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨35,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨36,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨37,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨38,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨39,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨40,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨41,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨42,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨43,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨44,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨45,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨46,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨47,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨48,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨49,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨50,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨51,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12821) (by norm_num)
        (q := 1 - (cell12821 ⟨52,by decide⟩).lower)
        (by norm_num [cell12821]) (by norm_num [cell12821])
      exact ⟨E.1,E.2.trans (by norm_num [cell12821])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12821

/-! Source-cell containment and simple scalar guards at 12821. -/
namespace BstLean.Part269.N12821
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12821)
open BstLean.Part268 (cell12821)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12821 ⟨10,by decide⟩).lower ∧ (cell12821 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12821 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12821 ⟨11,by decide⟩).lower ∧ (cell12821 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12821 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12821 ⟨12,by decide⟩).lower ∧ (cell12821 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12821 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12821 ⟨13,by decide⟩).lower ∧ (cell12821 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12821 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12821 ⟨14,by decide⟩).lower ∧ (cell12821 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12821 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12821 ⟨15,by decide⟩).lower ∧ (cell12821 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12821 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12821 ⟨16,by decide⟩).lower ∧ (cell12821 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12821 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12821 ⟨17,by decide⟩).lower ∧ (cell12821 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12821 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12821 ⟨18,by decide⟩).lower ∧ (cell12821 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12821 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12821 ⟨19,by decide⟩).lower ∧ (cell12821 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12821 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12821 ⟨20,by decide⟩).lower ∧ (cell12821 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12821 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12821 ⟨21,by decide⟩).lower ∧ (cell12821 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12821 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12821 ⟨22,by decide⟩).lower ∧ (cell12821 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12821 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12821 ⟨23,by decide⟩).lower ∧ (cell12821 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12821 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12821 ⟨24,by decide⟩).lower ∧ (cell12821 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12821 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12821 ⟨25,by decide⟩).lower ∧ (cell12821 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12821 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12821 ⟨26,by decide⟩).lower ∧ (cell12821 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12821 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12821 ⟨27,by decide⟩).lower ∧ (cell12821 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12821 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12821 ⟨28,by decide⟩).lower ∧ (cell12821 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12821 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12821 ⟨29,by decide⟩).lower ∧ (cell12821 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12821 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12821 ⟨30,by decide⟩).lower ∧ (cell12821 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12821 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12821 ⟨31,by decide⟩).lower ∧ (cell12821 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12821 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12821 ⟨32,by decide⟩).lower ∧ (cell12821 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12821 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12821 ⟨33,by decide⟩).lower ∧ (cell12821 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12821 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12821 ⟨34,by decide⟩).lower ∧ (cell12821 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12821 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12821 ⟨35,by decide⟩).lower ∧ (cell12821 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12821 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12821 ⟨36,by decide⟩).lower ∧ (cell12821 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12821 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12821 ⟨37,by decide⟩).lower ∧ (cell12821 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12821 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12821 ⟨38,by decide⟩).lower ∧ (cell12821 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12821 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12821 ⟨39,by decide⟩).lower ∧ (cell12821 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12821 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12821 ⟨40,by decide⟩).lower ∧ (cell12821 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12821 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12821 ⟨41,by decide⟩).lower ∧ (cell12821 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12821 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12821 ⟨42,by decide⟩).lower ∧ (cell12821 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12821 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12821 ⟨43,by decide⟩).lower ∧ (cell12821 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12821 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12821 ⟨44,by decide⟩).lower ∧ (cell12821 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12821 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12821 ⟨45,by decide⟩).lower ∧ (cell12821 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12821 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12821 ⟨46,by decide⟩).lower ∧ (cell12821 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12821 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12821 ⟨47,by decide⟩).lower ∧ (cell12821 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12821 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12821 ⟨48,by decide⟩).lower ∧ (cell12821 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12821 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12821 ⟨49,by decide⟩).lower ∧ (cell12821 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12821 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12821 ⟨50,by decide⟩).lower ∧ (cell12821 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12821 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12821 ⟨51,by decide⟩).lower ∧ (cell12821 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12821 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12821 ⟨52,by decide⟩).lower ∧ (cell12821 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12821 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12821 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12821 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12821,cell12821,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12821 i).lower ∧
    (cell12821 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12821 i).upper ≤ (0.532 : ℝ) ∧
    (cell12821 i).centre ≤ (0.1 : ℝ) ∧ (cell12821 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12821 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12821 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12821

/-! The local source numeric instances at 12821 have no network premises. -/
namespace BstLean.Part269.N12821
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12821)
open BstLean.Part268 (cell12821)

noncomputable def sourceNumerics12821 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12821 (cell12821 i)
      scalarRow12821.M scalarRow12821.H scalarRow12821.xi := by
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
    energy_allowance := scalarRow12821.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12821]
    centre_nonneg := (scalarRow12821.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12821])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12821
/-! Actual 12822 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12822
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12822 ≤ (1.035636958488 : ℝ) := by
  have hr : (113.234270430819 : ℝ) ≤ √(12822 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.234270430819 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12822 12822 (11 / 1000) ≤
    (0.008441675745 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12822) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.234270430819 : ℝ) ≤ √(12822 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12822)
  have hdiv : K / √(12822 : ℝ) ≤ K / 113.234270430819 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.234270430819 ≤ (0.008441675745 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12822.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12822 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12822 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12822 := gPlus_lower 12822
end BstLean.Part269.N12822

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12822
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035636958487 : ℝ) ≤ wn 12822 := by
  have hn : √(12822 : ℝ) ≤ 113.234270430820 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12822 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.234270430820 ≤ 2 / √(12822 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249442758 : ℝ) ≤ rhoBar 12822 BstLean.Part154.csC ∧
    rhoBar 12822 BstLean.Part154.csC ≤ 0.000249443144 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035636958487 : ℝ) / (1.295212 * 12822) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035636958488 : ℝ) / (1.29521 * 12822) := by gcongr
      _ ≤ (0.000249443144 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12822 BstLean.Part154.csC) ≤ 0.000997834798 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12822 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12822 BstLean.Part154.csC) (piBar (rhoBar 12822 BstLean.Part154.csC)) ≤ 0.000190526270 ∧
    cc1 (rhoBar 12822 BstLean.Part154.csC) (piBar (rhoBar 12822 BstLean.Part154.csC)) ≤ 0.000121233149 ∧
    cc2 (rhoBar 12822 BstLean.Part154.csC) ≤ 0.000070376793 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12822 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12822 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12822 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12822 BstLean.Part154.csC * nuR (rhoBar 12822 BstLean.Part154.csC)) ≤ 0.000498901844 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249443144 : ℝ) * 0.000997834798 := by gcongr
      _ ≤ (0.000498901844 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12822 BstLean.Part154.csC) * nuR (rhoBar 12822 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000997834798 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12822 BstLean.Part154.csC) * rhoBar 12822 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249443144 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249443144 / 2 + 0.399 * 0.000997834798 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190526270 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498901844 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121233149 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249443144 / 1.414213562 := by gcongr
      _ ≤ (0.000070376793 : ℝ) := by norm_num

end BstLean.Part269.N12822

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12822
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12822 BstLean.Part154.csC) (piBar (rhoBar 12822 BstLean.Part154.csC)) ≤ 1.56764E-7 := by
  have hr0 : 0 ≤ rhoBar 12822 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12822 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12822 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12822 BstLean.Part154.csC) (piBar (rhoBar 12822 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12822 BstLean.Part154.csC) (piBar (rhoBar 12822 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12822 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190526270 : ℝ) ^ 2 + 0.000121233149 ^ 2 + 3 * 0.000070376793 ^ 2 +
        2 * 0.797885 * 0.000190526270 * 0.000121233149 + 2 * 0.000190526270 * 0.000070376793 +
        4 * 0.797885 * 0.000121233149 * 0.000070376793 := by gcongr
    _ ≤ (1.56764E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12822 BstLean.Part154.csC Θ ≤ 0.002603412398 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12822 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12822 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12822 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12822 BstLean.Part154.csC) (piBar (rhoBar 12822 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12822 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035636958488 * 1.56764E-7 / (0.000249442758 : ℝ) := by gcongr
    _ ≤ 0.002603412398 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12822 BstLean.Part154.csC Θ ≤ 0.002888136653 + 0.000657838546 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12822 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12822 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12822 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035636958488 : ℝ) * ((2 * Θ * 0.000249443144 +
        (6863 / 10000) * 0.000249443144 * 12822 * 0.000997834798) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002888136653 + 0.000657838546 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12822 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12822 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12822 0.011 Θ ∧ gammaRatio 12822 0.011 Θ ≤ 0.000085752103 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12822 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035636958488 : ℝ) * 0.525 / ((1 - 0.011) * 12822) := by gcongr
      _ ≤ (0.000085752103 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12822 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12822 0.011 Θ) :=
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
    badAllowance 12822 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12822 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12822 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12822 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12822 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12822 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12822 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12822 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12822 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12822 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12822 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035636958488 : ℝ) * 12822 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12822 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003396941153 + 0.003261250944 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12822

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12822
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12822 BstLean.Part154.csC) (piBar (rhoBar 12822 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12822 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12822 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12822 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12822 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12822 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12822 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12822 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12822 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12822 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12822 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12822 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12822 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12822 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12822 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052231323561 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12822) ≤ 0.010546609048 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12822 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035636958488)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010546609048 + 2 * 0.737676 / 12822) := by gcongr
    _ ≤ (0.052231323561 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12822 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12822

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12822
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509032997 : ℝ) ≤ plow 12822 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12822) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052615697899)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366791509) : eMP 12822 0.011 xi bn ≤ 0.001176839641 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12822 : ℝ) * (1 - 0.011))) ≤ 0.000581902288 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001366791509 / (12822 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581902288 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581902288 : ℝ) + 3.141593 * 0.052615697899 / (12822 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001176839641 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052615697899)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366791509) : PiBarMP 12822 12 0.011 xi bn ≤ 0.160474290726 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12822 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036970143481 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.609759790170 : ℝ) ≤ √((12822 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.234270430819 : ℝ) ≤ √(12822 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12822) ≤ 0.123040561924 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036970143481 + 0.052615697899 * 1.772454 / (2 * (112.609759790170 : ℝ))) * (1 + 0.001176839641) +
        8 / (12822 * 113.234270430819) + 0.123040561924 := by gcongr
    _ ≤ (0.160474290726 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052615697899)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366791509) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281612442878) :
    parallelOracle 12822 0.011 xi bn cd ≤ 0.161455064456 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12822 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12822 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509032997 : ℝ) ≤ plow 12822 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.234270430819 : ℝ) ≤ √(12822 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281612442878 : ℝ) / (2 * 0.560509032997 * 113.234270430819)) * 0.160474290726 +
        0.281612442878 ^ 2 / (2 * 0.560509032997 * 113.234270430819) := by gcongr
    _ ≤ (0.161455064456 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052615697899) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366791509)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281612442878) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12822 12822 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509032997 : ℝ) ≤ plow 12822 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.234270430819 : ℝ) ≤ √(12822 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12822 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12822 Θ 1.22 ≤ 0.011711123276 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.234270430819 := by gcongr <;> linarith
      _ ≤ (0.011711123276 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12822 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12822 12822 0.011 ≤ 0.008441675745 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12822 12822 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12822 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12822 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12822 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12822 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161455064456 + 0.011711123276 + (0.008441675745 : ℝ) *
        (1 + 2 * (0.281612442878 + 0.011711123276) / (0.560509032997 * 113.234270430819))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12822]

end BstLean.Part269.N12822

/-! The original eight local profiles supply actual 12822 moment certificates. -/
namespace BstLean.Part269.N12822
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12822 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12822 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12822 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052615697899 ∧
    0 ≤ bN 12822 BstLean.Part154.csC (groupTheta g) ∧ bN 12822 BstLean.Part154.csC (groupTheta g) ≤ 0.001366791509 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12822 12822 0.011
      (momentAllowance 12822 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12822 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12822 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12822 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12822 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12822 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229381119317 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12822 0.011
      (momentAllowance 12822 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12822 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12822
/-! The actual computed-centre upper energy formula at 12822. -/
namespace BstLean.Part269.N12822
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12822

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12822
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12822)
open BstLean.Part268 (cell12822)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085142215363
  | 2 => 0.086078742369
  | 3 => 0.087012529340
  | 4 => 0.087944789772
  | 5 => 0.088876997883
  | 6 => 0.089810928156
  | 7 => 0.090748698759
  | 8 => 0.091692818905
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12822 12822 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12822 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12822

/-! Actual upper energy certificates on all 43 source endpoints at 12822. -/
namespace BstLean.Part269.N12822
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12822)
open BstLean.Part268 (cell12822)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12822 (gMinus 12822) (1 - (cell12822 i).lower) ≤ 1 ∧
    energyUpper 12822 (gMinus 12822) (BstLean.Part211.gPlus 12822)
      (finiteEnergy 12822 12822 0.011) (1 - (cell12822 i).lower) ≤
      (cell12822 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨10,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨11,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨12,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨13,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨14,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨15,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨16,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨17,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨18,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨19,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨20,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨21,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨22,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨23,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨24,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨25,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨26,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨27,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨28,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨29,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨30,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨31,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨32,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨33,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨34,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨35,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨36,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨37,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨38,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨39,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨40,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨41,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨42,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨43,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨44,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨45,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨46,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨47,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨48,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨49,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨50,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨51,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12822) (by norm_num)
        (q := 1 - (cell12822 ⟨52,by decide⟩).lower)
        (by norm_num [cell12822]) (by norm_num [cell12822])
      exact ⟨E.1,E.2.trans (by norm_num [cell12822])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12822

/-! Source-cell containment and simple scalar guards at 12822. -/
namespace BstLean.Part269.N12822
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12822)
open BstLean.Part268 (cell12822)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12822 ⟨10,by decide⟩).lower ∧ (cell12822 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12822 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12822 ⟨11,by decide⟩).lower ∧ (cell12822 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12822 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12822 ⟨12,by decide⟩).lower ∧ (cell12822 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12822 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12822 ⟨13,by decide⟩).lower ∧ (cell12822 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12822 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12822 ⟨14,by decide⟩).lower ∧ (cell12822 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12822 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12822 ⟨15,by decide⟩).lower ∧ (cell12822 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12822 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12822 ⟨16,by decide⟩).lower ∧ (cell12822 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12822 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12822 ⟨17,by decide⟩).lower ∧ (cell12822 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12822 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12822 ⟨18,by decide⟩).lower ∧ (cell12822 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12822 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12822 ⟨19,by decide⟩).lower ∧ (cell12822 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12822 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12822 ⟨20,by decide⟩).lower ∧ (cell12822 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12822 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12822 ⟨21,by decide⟩).lower ∧ (cell12822 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12822 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12822 ⟨22,by decide⟩).lower ∧ (cell12822 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12822 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12822 ⟨23,by decide⟩).lower ∧ (cell12822 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12822 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12822 ⟨24,by decide⟩).lower ∧ (cell12822 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12822 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12822 ⟨25,by decide⟩).lower ∧ (cell12822 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12822 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12822 ⟨26,by decide⟩).lower ∧ (cell12822 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12822 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12822 ⟨27,by decide⟩).lower ∧ (cell12822 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12822 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12822 ⟨28,by decide⟩).lower ∧ (cell12822 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12822 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12822 ⟨29,by decide⟩).lower ∧ (cell12822 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12822 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12822 ⟨30,by decide⟩).lower ∧ (cell12822 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12822 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12822 ⟨31,by decide⟩).lower ∧ (cell12822 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12822 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12822 ⟨32,by decide⟩).lower ∧ (cell12822 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12822 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12822 ⟨33,by decide⟩).lower ∧ (cell12822 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12822 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12822 ⟨34,by decide⟩).lower ∧ (cell12822 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12822 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12822 ⟨35,by decide⟩).lower ∧ (cell12822 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12822 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12822 ⟨36,by decide⟩).lower ∧ (cell12822 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12822 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12822 ⟨37,by decide⟩).lower ∧ (cell12822 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12822 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12822 ⟨38,by decide⟩).lower ∧ (cell12822 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12822 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12822 ⟨39,by decide⟩).lower ∧ (cell12822 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12822 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12822 ⟨40,by decide⟩).lower ∧ (cell12822 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12822 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12822 ⟨41,by decide⟩).lower ∧ (cell12822 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12822 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12822 ⟨42,by decide⟩).lower ∧ (cell12822 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12822 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12822 ⟨43,by decide⟩).lower ∧ (cell12822 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12822 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12822 ⟨44,by decide⟩).lower ∧ (cell12822 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12822 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12822 ⟨45,by decide⟩).lower ∧ (cell12822 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12822 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12822 ⟨46,by decide⟩).lower ∧ (cell12822 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12822 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12822 ⟨47,by decide⟩).lower ∧ (cell12822 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12822 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12822 ⟨48,by decide⟩).lower ∧ (cell12822 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12822 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12822 ⟨49,by decide⟩).lower ∧ (cell12822 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12822 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12822 ⟨50,by decide⟩).lower ∧ (cell12822 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12822 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12822 ⟨51,by decide⟩).lower ∧ (cell12822 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12822 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12822 ⟨52,by decide⟩).lower ∧ (cell12822 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12822 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12822 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12822 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12822,cell12822,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12822 i).lower ∧
    (cell12822 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12822 i).upper ≤ (0.532 : ℝ) ∧
    (cell12822 i).centre ≤ (0.1 : ℝ) ∧ (cell12822 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12822 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12822 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12822

/-! The local source numeric instances at 12822 have no network premises. -/
namespace BstLean.Part269.N12822
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12822)
open BstLean.Part268 (cell12822)

noncomputable def sourceNumerics12822 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12822 (cell12822 i)
      scalarRow12822.M scalarRow12822.H scalarRow12822.xi := by
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
    energy_allowance := scalarRow12822.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12822]
    centre_nonneg := (scalarRow12822.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12822])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12822
/-! Actual 12823 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12823
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12823 ≤ (1.035635556725 : ℝ) := by
  have hr : (113.238685969062 : ℝ) ≤ √(12823 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.238685969062 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12823 12823 (11 / 1000) ≤
    (0.008441346574 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12823) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.238685969062 : ℝ) ≤ √(12823 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12823)
  have hdiv : K / √(12823 : ℝ) ≤ K / 113.238685969062 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.238685969062 ≤ (0.008441346574 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12823.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12823 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12823 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12823 := gPlus_lower 12823
end BstLean.Part269.N12823

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12823
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035635556724 : ℝ) ≤ wn 12823 := by
  have hn : √(12823 : ℝ) ≤ 113.238685969063 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12823 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.238685969063 ≤ 2 / √(12823 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249422967 : ℝ) ≤ rhoBar 12823 BstLean.Part154.csC ∧
    rhoBar 12823 BstLean.Part154.csC ≤ 0.000249423353 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035635556724 : ℝ) / (1.295212 * 12823) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035635556725 : ℝ) / (1.29521 * 12823) := by gcongr
      _ ≤ (0.000249423353 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12823 BstLean.Part154.csC) ≤ 0.000997755625 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12823 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12823 BstLean.Part154.csC) (piBar (rhoBar 12823 BstLean.Part154.csC)) ≤ 0.000190511153 ∧
    cc1 (rhoBar 12823 BstLean.Part154.csC) (piBar (rhoBar 12823 BstLean.Part154.csC)) ≤ 0.000121223530 ∧
    cc2 (rhoBar 12823 BstLean.Part154.csC) ≤ 0.000070371209 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12823 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12823 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12823 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12823 BstLean.Part154.csC * nuR (rhoBar 12823 BstLean.Part154.csC)) ≤ 0.000498862260 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249423353 : ℝ) * 0.000997755625 := by gcongr
      _ ≤ (0.000498862260 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12823 BstLean.Part154.csC) * nuR (rhoBar 12823 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000997755625 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12823 BstLean.Part154.csC) * rhoBar 12823 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249423353 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249423353 / 2 + 0.399 * 0.000997755625 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190511153 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498862260 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121223530 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249423353 / 1.414213562 := by gcongr
      _ ≤ (0.000070371209 : ℝ) := by norm_num

end BstLean.Part269.N12823

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12823
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12823 BstLean.Part154.csC) (piBar (rhoBar 12823 BstLean.Part154.csC)) ≤ 1.56739E-7 := by
  have hr0 : 0 ≤ rhoBar 12823 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12823 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12823 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12823 BstLean.Part154.csC) (piBar (rhoBar 12823 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12823 BstLean.Part154.csC) (piBar (rhoBar 12823 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12823 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190511153 : ℝ) ^ 2 + 0.000121223530 ^ 2 + 3 * 0.000070371209 ^ 2 +
        2 * 0.797885 * 0.000190511153 * 0.000121223530 + 2 * 0.000190511153 * 0.000070371209 +
        4 * 0.797885 * 0.000121223530 * 0.000070371209 := by gcongr
    _ ≤ (1.56739E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12823 BstLean.Part154.csC Θ ≤ 0.002603200235 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12823 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12823 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12823 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12823 BstLean.Part154.csC) (piBar (rhoBar 12823 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12823 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035635556725 * 1.56739E-7 / (0.000249422967 : ℝ) := by gcongr
    _ ≤ 0.002603200235 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12823 BstLean.Part154.csC Θ ≤ 0.002887899669 + 0.000657785462 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12823 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12823 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12823 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035635556725 : ℝ) * ((2 * Θ * 0.000249423353 +
        (6863 / 10000) * 0.000249423353 * 12823 * 0.000997755625) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002887899669 + 0.000657785462 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12823 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12823 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12823 0.011 Θ ∧ gammaRatio 12823 0.011 Θ ≤ 0.000085745299 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12823 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035635556725 : ℝ) * 0.525 / ((1 - 0.011) * 12823) := by gcongr
      _ ≤ (0.000085745299 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12823 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12823 0.011 Θ) :=
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
    badAllowance 12823 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12823 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12823 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12823 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12823 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12823 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12823 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12823 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12823 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12823 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12823 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035635556725 : ℝ) * 12823 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12823 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003396704169 + 0.003260985697 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12823

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12823
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12823 BstLean.Part154.csC) (piBar (rhoBar 12823 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12823 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12823 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12823 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12823 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12823 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12823 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12823 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12823 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12823 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12823 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12823 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12823 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12823 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12823 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052229264915 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12823) ≤ 0.010546197802 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12823 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035635556725)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010546197802 + 2 * 0.737676 / 12823) := by gcongr
    _ ≤ (0.052229264915 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12823 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12823

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12823
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509077360 : ℝ) ≤ plow 12823 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12823) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052615321660)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366680124) : eMP 12823 0.011 xi bn ≤ 0.001176745729 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12823 : ℝ) * (1 - 0.011))) ≤ 0.000581855887 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001366680124 / (12823 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581855887 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581855887 : ℝ) + 3.141593 * 0.052615321660 / (12823 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001176745729 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052615321660)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366680124) : PiBarMP 12823 12 0.011 xi bn ≤ 0.160467961475 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12823 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036968637032 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.614150975798 : ℝ) ≤ √((12823 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.238685969062 : ℝ) ≤ √(12823 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12823) ≤ 0.123035764179 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036968637032 + 0.052615321660 * 1.772454 / (2 * (112.614150975798 : ℝ))) * (1 + 0.001176745729) +
        8 / (12823 * 113.238685969062) + 0.123035764179 := by gcongr
    _ ≤ (0.160467961475 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052615321660)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366680124) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281609564113) :
    parallelOracle 12823 0.011 xi bn cd ≤ 0.161448666431 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12823 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12823 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509077360 : ℝ) ≤ plow 12823 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.238685969062 : ℝ) ≤ √(12823 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281609564113 : ℝ) / (2 * 0.560509077360 * 113.238685969062)) * 0.160467961475 +
        0.281609564113 ^ 2 / (2 * 0.560509077360 * 113.238685969062) := by gcongr
    _ ≤ (0.161448666431 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052615321660) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366680124)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281609564113) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12823 12823 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509077360 : ℝ) ≤ plow 12823 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.238685969062 : ℝ) ≤ √(12823 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12823 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12823 Θ 1.22 ≤ 0.011710666622 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.238685969062 := by gcongr <;> linarith
      _ ≤ (0.011710666622 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12823 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12823 12823 0.011 ≤ 0.008441346574 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12823 12823 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12823 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12823 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12823 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12823 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161448666431 + 0.011710666622 + (0.008441346574 : ℝ) *
        (1 + 2 * (0.281609564113 + 0.011710666622) / (0.560509077360 * 113.238685969062))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12823]

end BstLean.Part269.N12823

/-! The original eight local profiles supply actual 12823 moment certificates. -/
namespace BstLean.Part269.N12823
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12823 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12823 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12823 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052615321660 ∧
    0 ≤ bN 12823 BstLean.Part154.csC (groupTheta g) ∧ bN 12823 BstLean.Part154.csC (groupTheta g) ≤ 0.001366680124 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12823 12823 0.011
      (momentAllowance 12823 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12823 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12823 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12823 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12823 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12823 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229380299198 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12823 0.011
      (momentAllowance 12823 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12823 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12823
/-! The actual computed-centre upper energy formula at 12823. -/
namespace BstLean.Part269.N12823
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12823

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12823
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12823)
open BstLean.Part268 (cell12823)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085139424031
  | 2 => 0.086075902498
  | 3 => 0.087009634299
  | 4 => 0.087941831373
  | 5 => 0.088873966100
  | 6 => 0.089807810809
  | 7 => 0.090745481160
  | 8 => 0.091689483464
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12823 12823 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12823 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12823

/-! Actual upper energy certificates on all 43 source endpoints at 12823. -/
namespace BstLean.Part269.N12823
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12823)
open BstLean.Part268 (cell12823)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12823 (gMinus 12823) (1 - (cell12823 i).lower) ≤ 1 ∧
    energyUpper 12823 (gMinus 12823) (BstLean.Part211.gPlus 12823)
      (finiteEnergy 12823 12823 0.011) (1 - (cell12823 i).lower) ≤
      (cell12823 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨10,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨11,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨12,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨13,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨14,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨15,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨16,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨17,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨18,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨19,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨20,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨21,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨22,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨23,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨24,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨25,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨26,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨27,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨28,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨29,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨30,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨31,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨32,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨33,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨34,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨35,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨36,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨37,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨38,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨39,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨40,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨41,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨42,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨43,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨44,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨45,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨46,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨47,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨48,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨49,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨50,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨51,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12823) (by norm_num)
        (q := 1 - (cell12823 ⟨52,by decide⟩).lower)
        (by norm_num [cell12823]) (by norm_num [cell12823])
      exact ⟨E.1,E.2.trans (by norm_num [cell12823])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12823

/-! Source-cell containment and simple scalar guards at 12823. -/
namespace BstLean.Part269.N12823
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12823)
open BstLean.Part268 (cell12823)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12823 ⟨10,by decide⟩).lower ∧ (cell12823 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12823 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12823 ⟨11,by decide⟩).lower ∧ (cell12823 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12823 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12823 ⟨12,by decide⟩).lower ∧ (cell12823 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12823 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12823 ⟨13,by decide⟩).lower ∧ (cell12823 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12823 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12823 ⟨14,by decide⟩).lower ∧ (cell12823 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12823 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12823 ⟨15,by decide⟩).lower ∧ (cell12823 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12823 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12823 ⟨16,by decide⟩).lower ∧ (cell12823 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12823 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12823 ⟨17,by decide⟩).lower ∧ (cell12823 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12823 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12823 ⟨18,by decide⟩).lower ∧ (cell12823 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12823 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12823 ⟨19,by decide⟩).lower ∧ (cell12823 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12823 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12823 ⟨20,by decide⟩).lower ∧ (cell12823 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12823 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12823 ⟨21,by decide⟩).lower ∧ (cell12823 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12823 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12823 ⟨22,by decide⟩).lower ∧ (cell12823 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12823 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12823 ⟨23,by decide⟩).lower ∧ (cell12823 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12823 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12823 ⟨24,by decide⟩).lower ∧ (cell12823 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12823 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12823 ⟨25,by decide⟩).lower ∧ (cell12823 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12823 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12823 ⟨26,by decide⟩).lower ∧ (cell12823 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12823 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12823 ⟨27,by decide⟩).lower ∧ (cell12823 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12823 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12823 ⟨28,by decide⟩).lower ∧ (cell12823 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12823 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12823 ⟨29,by decide⟩).lower ∧ (cell12823 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12823 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12823 ⟨30,by decide⟩).lower ∧ (cell12823 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12823 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12823 ⟨31,by decide⟩).lower ∧ (cell12823 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12823 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12823 ⟨32,by decide⟩).lower ∧ (cell12823 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12823 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12823 ⟨33,by decide⟩).lower ∧ (cell12823 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12823 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12823 ⟨34,by decide⟩).lower ∧ (cell12823 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12823 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12823 ⟨35,by decide⟩).lower ∧ (cell12823 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12823 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12823 ⟨36,by decide⟩).lower ∧ (cell12823 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12823 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12823 ⟨37,by decide⟩).lower ∧ (cell12823 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12823 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12823 ⟨38,by decide⟩).lower ∧ (cell12823 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12823 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12823 ⟨39,by decide⟩).lower ∧ (cell12823 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12823 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12823 ⟨40,by decide⟩).lower ∧ (cell12823 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12823 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12823 ⟨41,by decide⟩).lower ∧ (cell12823 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12823 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12823 ⟨42,by decide⟩).lower ∧ (cell12823 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12823 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12823 ⟨43,by decide⟩).lower ∧ (cell12823 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12823 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12823 ⟨44,by decide⟩).lower ∧ (cell12823 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12823 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12823 ⟨45,by decide⟩).lower ∧ (cell12823 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12823 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12823 ⟨46,by decide⟩).lower ∧ (cell12823 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12823 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12823 ⟨47,by decide⟩).lower ∧ (cell12823 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12823 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12823 ⟨48,by decide⟩).lower ∧ (cell12823 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12823 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12823 ⟨49,by decide⟩).lower ∧ (cell12823 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12823 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12823 ⟨50,by decide⟩).lower ∧ (cell12823 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12823 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12823 ⟨51,by decide⟩).lower ∧ (cell12823 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12823 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12823 ⟨52,by decide⟩).lower ∧ (cell12823 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12823 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12823 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12823 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12823,cell12823,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12823 i).lower ∧
    (cell12823 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12823 i).upper ≤ (0.532 : ℝ) ∧
    (cell12823 i).centre ≤ (0.1 : ℝ) ∧ (cell12823 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12823 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12823 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12823

/-! The local source numeric instances at 12823 have no network premises. -/
namespace BstLean.Part269.N12823
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12823)
open BstLean.Part268 (cell12823)

noncomputable def sourceNumerics12823 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12823 (cell12823 i)
      scalarRow12823.M scalarRow12823.H scalarRow12823.xi := by
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
    energy_allowance := scalarRow12823.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12823]
    centre_nonneg := (scalarRow12823.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12823])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12823
/-! Actual 12824 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12824
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12824 ≤ (1.035634155127 : ℝ) := by
  have hr : (113.243101335136 : ℝ) ≤ √(12824 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.243101335136 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12824 12824 (11 / 1000) ≤
    (0.008441017442 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12824) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.243101335136 : ℝ) ≤ √(12824 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12824)
  have hdiv : K / √(12824 : ℝ) ≤ K / 113.243101335136 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.243101335136 ≤ (0.008441017442 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12824.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12824 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12824 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12824 := gPlus_lower 12824
end BstLean.Part269.N12824

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12824
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035634155126 : ℝ) ≤ wn 12824 := by
  have hn : √(12824 : ℝ) ≤ 113.243101335137 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12824 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.243101335137 ≤ 2 / √(12824 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000249403180 : ℝ) ≤ rhoBar 12824 BstLean.Part154.csC ∧
    rhoBar 12824 BstLean.Part154.csC ≤ 0.000249403566 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035634155126 : ℝ) / (1.295212 * 12824) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035634155127 : ℝ) / (1.29521 * 12824) := by gcongr
      _ ≤ (0.000249403566 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12824 BstLean.Part154.csC) ≤ 0.000997676467 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12824 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12824 BstLean.Part154.csC) (piBar (rhoBar 12824 BstLean.Part154.csC)) ≤ 0.000190496039 ∧
    cc1 (rhoBar 12824 BstLean.Part154.csC) (piBar (rhoBar 12824 BstLean.Part154.csC)) ≤ 0.000121213912 ∧
    cc2 (rhoBar 12824 BstLean.Part154.csC) ≤ 0.000070365627 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12824 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12824 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12824 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12824 BstLean.Part154.csC * nuR (rhoBar 12824 BstLean.Part154.csC)) ≤ 0.000498822683 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000249403566 : ℝ) * 0.000997676467 := by gcongr
      _ ≤ (0.000498822683 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12824 BstLean.Part154.csC) * nuR (rhoBar 12824 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000997676467 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12824 BstLean.Part154.csC) * rhoBar 12824 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000249403566 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000249403566 / 2 + 0.399 * 0.000997676467 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000190496039 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000498822683 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000121213912 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000249403566 / 1.414213562 := by gcongr
      _ ≤ (0.000070365627 : ℝ) := by norm_num

end BstLean.Part269.N12824

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12824
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12824 BstLean.Part154.csC) (piBar (rhoBar 12824 BstLean.Part154.csC)) ≤ 1.56714E-7 := by
  have hr0 : 0 ≤ rhoBar 12824 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12824 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12824 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12824 BstLean.Part154.csC) (piBar (rhoBar 12824 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12824 BstLean.Part154.csC) (piBar (rhoBar 12824 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12824 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000190496039 : ℝ) ^ 2 + 0.000121213912 ^ 2 + 3 * 0.000070365627 ^ 2 +
        2 * 0.797885 * 0.000190496039 * 0.000121213912 + 2 * 0.000190496039 * 0.000070365627 +
        4 * 0.797885 * 0.000121213912 * 0.000070365627 := by gcongr
    _ ≤ (1.56714E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12824 BstLean.Part154.csC Θ ≤ 0.002602987997 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12824 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12824 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12824 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12824 BstLean.Part154.csC) (piBar (rhoBar 12824 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12824 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035634155127 * 1.56714E-7 / (0.000249403180 : ℝ) := by gcongr
    _ ≤ 0.002602987997 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12824 BstLean.Part154.csC Θ ≤ 0.002887662742 + 0.000657732389 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12824 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12824 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12824 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035634155127 : ℝ) * ((2 * Θ * 0.000249403566 +
        (6863 / 10000) * 0.000249403566 * 12824 * 0.000997676467) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002887662742 + 0.000657732389 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12824 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12824 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12824 0.011 Θ ∧ gammaRatio 12824 0.011 Θ ≤ 0.000085738497 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12824 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035634155127 : ℝ) * 0.525 / ((1 - 0.011) * 12824) := by gcongr
      _ ≤ (0.000085738497 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12824 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12824 0.011 Θ) :=
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
    badAllowance 12824 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000508804500 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12824 BstLean.Part154.csC) 1.22 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 2 (rhoBar 12824 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12824 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12824 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12824 0.011 Θ) 1.12 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 1 (gammaRatio 12824 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12824 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12824 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12824 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12824 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035634155127 : ℝ) * 12824 *
        (1.8602E-8 / 1.1045361 + 2.2721E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000508804500 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12824 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003396467242 + 0.003260720386 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12824

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12824
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12824 BstLean.Part154.csC) (piBar (rhoBar 12824 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12824 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12824 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12824 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12824 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12824 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12824 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12824 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12824 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12824 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12824 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12824 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12824 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12824 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12824 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052227206512 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12824) ≤ 0.010545786604 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12824 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035634155127)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010545786604 + 2 * 0.737676 / 12824) := by gcongr
    _ ≤ (0.052227206512 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12824 12 ≤ 0.0015 := by
  exact BstLean.Part269.S18.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12824

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12824
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560509121717 : ℝ) ≤ plow 12824 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12824) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052614945445)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366568699) : eMP 12824 0.011 xi bn ≤ 0.001176651810 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12824 : ℝ) * (1 - 0.011))) ≤ 0.000581809482 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001366568699 / (12824 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000581809482 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000581809482 : ℝ) + 3.141593 * 0.052614945445 / (12824 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001176651810 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052614945445)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366568699) : PiBarMP 12824 12 0.011 xi bn ≤ 0.160461632184 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12824 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036967129981 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.618541990206 : ℝ) ≤ √((12824 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.243101335136 : ℝ) ≤ √(12824 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12824) ≤ 0.123030966995 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036967129981 + 0.052614945445 * 1.772454 / (2 * (112.618541990206 : ℝ))) * (1 + 0.001176651810) +
        8 / (12824 * 113.243101335136) + 0.123030966995 := by gcongr
    _ ≤ (0.160461632184 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052614945445)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366568699) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281606685640) :
    parallelOracle 12824 0.011 xi bn cd ≤ 0.161442268376 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12824 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12824 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560509121717 : ℝ) ≤ plow 12824 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.243101335136 : ℝ) ≤ √(12824 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281606685640 : ℝ) / (2 * 0.560509121717 * 113.243101335136)) * 0.160461632184 +
        0.281606685640 ^ 2 / (2 * 0.560509121717 * 113.243101335136) := by gcongr
    _ ≤ (0.161442268376 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052614945445) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001366568699)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281606685640) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12824 12824 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560509121717 : ℝ) ≤ plow 12824 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.243101335136 : ℝ) ≤ √(12824 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12824 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12824 Θ 1.22 ≤ 0.011710210021 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.243101335136 := by gcongr <;> linarith
      _ ≤ (0.011710210021 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12824 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12824 12824 0.011 ≤ 0.008441017442 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12824 12824 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12824 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12824 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12824 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12824 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161442268376 + 0.011710210021 + (0.008441017442 : ℝ) *
        (1 + 2 * (0.281606685640 + 0.011710210021) / (0.560509121717 * 113.243101335136))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12824]

end BstLean.Part269.N12824

/-! The original eight local profiles supply actual 12824 moment certificates. -/
namespace BstLean.Part269.N12824
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12824 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12824 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12824 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052614945445 ∧
    0 ≤ bN 12824 BstLean.Part154.csC (groupTheta g) ∧ bN 12824 BstLean.Part154.csC (groupTheta g) ≤ 0.001366568699 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12824 12824 0.011
      (momentAllowance 12824 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12824 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12824 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12824 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12824 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12824 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229379479128 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12824 0.011
      (momentAllowance 12824 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12824 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12824
/-! The actual computed-centre upper energy formula at 12824. -/
namespace BstLean.Part269.N12824
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12824

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12824
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12824)
open BstLean.Part268 (cell12824)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085136633657
  | 2 => 0.086073063623
  | 3 => 0.087006740302
  | 4 => 0.087938874076
  | 5 => 0.088870935489
  | 6 => 0.089804694720
  | 7 => 0.090742264922
  | 8 => 0.091686149511
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12824 12824 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12824 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003402164259 + 0.003267039105 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S18.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S18.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12824

/-! Actual upper energy certificates on all 43 source endpoints at 12824. -/
namespace BstLean.Part269.N12824
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12824)
open BstLean.Part268 (cell12824)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12824 (gMinus 12824) (1 - (cell12824 i).lower) ≤ 1 ∧
    energyUpper 12824 (gMinus 12824) (BstLean.Part211.gPlus 12824)
      (finiteEnergy 12824 12824 0.011) (1 - (cell12824 i).lower) ≤
      (cell12824 i).energy := by
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
      have E := BstLean.Part269.S18.uniformEnergy10 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨10,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy11 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨11,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy12 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨12,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy13 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨13,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy14 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨14,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy15 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨15,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy16 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨16,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy17 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨17,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy18 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨18,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy19 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨19,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy20 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨20,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy21 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨21,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy22 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨22,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy23 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨23,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy24 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨24,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy25 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨25,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy26 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨26,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy27 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨27,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy28 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨28,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy29 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨29,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy30 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨30,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy31 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨31,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy32 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨32,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy33 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨33,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy34 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨34,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy35 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨35,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy36 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨36,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy37 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨37,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy38 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨38,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy39 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨39,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy40 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨40,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy41 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨41,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy42 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨42,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy43 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨43,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy44 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨44,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy45 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨45,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy46 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨46,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy47 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨47,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy48 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨48,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy49 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨49,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy50 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨50,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy51 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨51,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S18.uniformEnergy52 (n := 12824) (by norm_num)
        (q := 1 - (cell12824 ⟨52,by decide⟩).lower)
        (by norm_num [cell12824]) (by norm_num [cell12824])
      exact ⟨E.1,E.2.trans (by norm_num [cell12824])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12824

/-! Source-cell containment and simple scalar guards at 12824. -/
namespace BstLean.Part269.N12824
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12824)
open BstLean.Part268 (cell12824)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12824 ⟨10,by decide⟩).lower ∧ (cell12824 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12824 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12824 ⟨11,by decide⟩).lower ∧ (cell12824 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12824 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12824 ⟨12,by decide⟩).lower ∧ (cell12824 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12824 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12824 ⟨13,by decide⟩).lower ∧ (cell12824 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12824 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12824 ⟨14,by decide⟩).lower ∧ (cell12824 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12824 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12824 ⟨15,by decide⟩).lower ∧ (cell12824 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12824 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12824 ⟨16,by decide⟩).lower ∧ (cell12824 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12824 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12824 ⟨17,by decide⟩).lower ∧ (cell12824 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12824 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12824 ⟨18,by decide⟩).lower ∧ (cell12824 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12824 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12824 ⟨19,by decide⟩).lower ∧ (cell12824 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12824 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12824 ⟨20,by decide⟩).lower ∧ (cell12824 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12824 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12824 ⟨21,by decide⟩).lower ∧ (cell12824 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12824 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12824 ⟨22,by decide⟩).lower ∧ (cell12824 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12824 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12824 ⟨23,by decide⟩).lower ∧ (cell12824 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12824 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12824 ⟨24,by decide⟩).lower ∧ (cell12824 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12824 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12824 ⟨25,by decide⟩).lower ∧ (cell12824 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12824 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12824 ⟨26,by decide⟩).lower ∧ (cell12824 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12824 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12824 ⟨27,by decide⟩).lower ∧ (cell12824 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12824 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12824 ⟨28,by decide⟩).lower ∧ (cell12824 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12824 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12824 ⟨29,by decide⟩).lower ∧ (cell12824 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12824 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12824 ⟨30,by decide⟩).lower ∧ (cell12824 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12824 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12824 ⟨31,by decide⟩).lower ∧ (cell12824 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12824 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12824 ⟨32,by decide⟩).lower ∧ (cell12824 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12824 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12824 ⟨33,by decide⟩).lower ∧ (cell12824 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12824 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12824 ⟨34,by decide⟩).lower ∧ (cell12824 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12824 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12824 ⟨35,by decide⟩).lower ∧ (cell12824 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12824 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12824 ⟨36,by decide⟩).lower ∧ (cell12824 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12824 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12824 ⟨37,by decide⟩).lower ∧ (cell12824 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12824 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12824 ⟨38,by decide⟩).lower ∧ (cell12824 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12824 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12824 ⟨39,by decide⟩).lower ∧ (cell12824 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12824 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12824 ⟨40,by decide⟩).lower ∧ (cell12824 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12824 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12824 ⟨41,by decide⟩).lower ∧ (cell12824 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12824 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12824 ⟨42,by decide⟩).lower ∧ (cell12824 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12824 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12824 ⟨43,by decide⟩).lower ∧ (cell12824 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12824 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12824 ⟨44,by decide⟩).lower ∧ (cell12824 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12824 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12824 ⟨45,by decide⟩).lower ∧ (cell12824 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12824 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12824 ⟨46,by decide⟩).lower ∧ (cell12824 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12824 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12824 ⟨47,by decide⟩).lower ∧ (cell12824 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12824 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12824 ⟨48,by decide⟩).lower ∧ (cell12824 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12824 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12824 ⟨49,by decide⟩).lower ∧ (cell12824 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12824 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12824 ⟨50,by decide⟩).lower ∧ (cell12824 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12824 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12824 ⟨51,by decide⟩).lower ∧ (cell12824 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12824 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12824 ⟨52,by decide⟩).lower ∧ (cell12824 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12824 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12824 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12824 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12824,cell12824,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12824 i).lower ∧
    (cell12824 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12824 i).upper ≤ (0.532 : ℝ) ∧
    (cell12824 i).centre ≤ (0.1 : ℝ) ∧ (cell12824 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12824 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12824 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12824

/-! The local source numeric instances at 12824 have no network premises. -/
namespace BstLean.Part269.N12824
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12824)
open BstLean.Part268 (cell12824)

noncomputable def sourceNumerics12824 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12824 (cell12824 i)
      scalarRow12824.M scalarRow12824.H scalarRow12824.xi := by
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
    energy_allowance := scalarRow12824.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12824]
    centre_nonneg := (scalarRow12824.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D18.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12824])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12824