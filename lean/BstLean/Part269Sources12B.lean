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
import BstLean.Part269Direction12
import BstLean.Part269Shared12
import BstLean.Part269Finite
import BstLean.Part269Rows12
import BstLean.Part269Source
/-! Actual 12663 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12663
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12663 ≤ (1.035861958778 : ℝ) := by
  have hr : (112.529996001066 : ℝ) ≤ √(12663 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.529996001066 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12663 12663 (11 / 1000) ≤
    (0.008494508787 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12663) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.529996001066 : ℝ) ≤ √(12663 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12663)
  have hdiv : K / √(12663 : ℝ) ≤ K / 112.529996001066 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.529996001066 ≤ (0.008494508787 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12663.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12663 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12663 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12663 := gPlus_lower 12663
end BstLean.Part269.N12663

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12663
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035861958777 : ℝ) ≤ wn 12663 := by
  have hn : √(12663 : ℝ) ≤ 112.529996001067 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12663 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.529996001067 ≤ 2 / √(12663 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252629701 : ℝ) ≤ rhoBar 12663 BstLean.Part154.csC ∧
    rhoBar 12663 BstLean.Part154.csC ≤ 0.000252630092 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035861958777 : ℝ) / (1.295212 * 12663) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035861958778 : ℝ) / (1.29521 * 12663) := by gcongr
      _ ≤ (0.000252630092 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12663 BstLean.Part154.csC) ≤ 0.001010584190 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12663 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12663 BstLean.Part154.csC) (piBar (rhoBar 12663 BstLean.Part154.csC)) ≤ 0.000192960595 ∧
    cc1 (rhoBar 12663 BstLean.Part154.csC) (piBar (rhoBar 12663 BstLean.Part154.csC)) ≤ 0.000122782103 ∧
    cc2 (rhoBar 12663 BstLean.Part154.csC) ≤ 0.000071275945 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12663 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12663 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12663 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12663 BstLean.Part154.csC * nuR (rhoBar 12663 BstLean.Part154.csC)) ≤ 0.000505276140 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252630092 : ℝ) * 0.001010584190 := by gcongr
      _ ≤ (0.000505276140 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12663 BstLean.Part154.csC) * nuR (rhoBar 12663 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001010584190 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12663 BstLean.Part154.csC) * rhoBar 12663 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252630092 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252630092 / 2 + 0.399 * 0.001010584190 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192960595 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505276140 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122782103 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252630092 / 1.414213562 := by gcongr
      _ ≤ (0.000071275945 : ℝ) := by norm_num

end BstLean.Part269.N12663

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12663
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12663 BstLean.Part154.csC) (piBar (rhoBar 12663 BstLean.Part154.csC)) ≤ 1.60795E-7 := by
  have hr0 : 0 ≤ rhoBar 12663 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12663 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12663 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12663 BstLean.Part154.csC) (piBar (rhoBar 12663 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12663 BstLean.Part154.csC) (piBar (rhoBar 12663 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12663 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192960595 : ℝ) ^ 2 + 0.000122782103 ^ 2 + 3 * 0.000071275945 ^ 2 +
        2 * 0.797885 * 0.000192960595 * 0.000122782103 + 2 * 0.000192960595 * 0.000071275945 +
        4 * 0.797885 * 0.000122782103 * 0.000071275945 := by gcongr
    _ ≤ (1.60795E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12663 BstLean.Part154.csC Θ ≤ 0.002637242146 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12663 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12663 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12663 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12663 BstLean.Part154.csC) (piBar (rhoBar 12663 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12663 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035861958778 * 1.60795E-7 / (0.000252629701 : ℝ) := by gcongr
    _ ≤ 0.002637242146 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12663 BstLean.Part154.csC Θ ≤ 0.002926309647 + 0.000666388002 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12663 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12663 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12663 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035861958778 : ℝ) * ((2 * Θ * 0.000252630092 +
        (6863 / 10000) * 0.000252630092 * 12663 * 0.001010584190) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002926309647 + 0.000666388002 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12663 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12663 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12663 0.011 Θ ∧ gammaRatio 12663 0.011 Θ ≤ 0.000086847693 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12663 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035861958778 : ℝ) * 0.525 / ((1 - 0.011) * 12663) := by gcongr
      _ ≤ (0.000086847693 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12663 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12663 0.011 Θ) :=
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
    badAllowance 12663 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12663 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12663 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12663 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12663 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12663 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12663 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12663 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12663 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12663 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12663 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035861958778 : ℝ) * 12663 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12663 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003540621038 + 0.003303630148 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12663

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12663
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12663 BstLean.Part154.csC) (piBar (rhoBar 12663 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12663 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12663 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12663 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12663 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12663 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12663 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12663 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12663 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12663 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12663 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12663 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12663 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12663 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12663 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052561765835 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12663) ≤ 0.010612615512 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12663 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035861958778)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010612615512 + 2 * 0.737676 / 12663) := by gcongr
    _ ≤ (0.052561765835 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12663 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12663

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12663
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501890152 : ℝ) ≤ plow 12663 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12663) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052781626866)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384552127) : eMP 12663 0.011 xi bn ≤ 0.001191912893 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12663 : ℝ) * (1 - 0.011))) ≤ 0.000589336266 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001384552127 / (12663 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589336266 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589336266 : ℝ) + 3.141593 * 0.052781626866 / (12663 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001191912893 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052781626866)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384552127) : PiBarMP 12663 12 0.011 xi bn ≤ 0.161488636122 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12663 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037209570369 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.909369580924 : ℝ) ≤ √((12663 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.529996001066 : ℝ) ≤ √(12663 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12663) ≤ 0.123810617239 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037209570369 + 0.052781626866 * 1.772454 / (2 * (111.909369580924 : ℝ))) * (1 + 0.001191912893) +
        8 / (12663 * 112.529996001066) + 0.123810617239 := by gcongr
    _ ≤ (0.161488636122 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052781626866)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384552127) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282304288817) :
    parallelOracle 12663 0.011 xi bn cd ≤ 0.162481803555 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12663 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12663 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501890152 : ℝ) ≤ plow 12663 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.529996001066 : ℝ) ≤ √(12663 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282304288817 : ℝ) / (2 * 0.560501890152 * 112.529996001066)) * 0.161488636122 +
        0.282304288817 ^ 2 / (2 * 0.560501890152 * 112.529996001066) := by gcongr
    _ ≤ (0.162481803555 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052781626866) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384552127)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282304288817) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12663 12663 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501890152 : ℝ) ≤ plow 12663 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.529996001066 : ℝ) ≤ √(12663 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12663 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12663 Θ 1.22 ≤ 0.011784417908 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.529996001066 := by gcongr <;> linarith
      _ ≤ (0.011784417908 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12663 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12663 12663 0.011 ≤ 0.008494508787 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12663 12663 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12663 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12663 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12663 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12663 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162481803555 + 0.011784417908 + (0.008494508787 : ℝ) *
        (1 + 2 * (0.282304288817 + 0.011784417908) / (0.560501890152 * 112.529996001066))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12663]

end BstLean.Part269.N12663

/-! The original eight local profiles supply actual 12663 moment certificates. -/
namespace BstLean.Part269.N12663
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12663 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12663 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12663 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052781626866 ∧
    0 ≤ bN 12663 BstLean.Part154.csC (groupTheta g) ∧ bN 12663 BstLean.Part154.csC (groupTheta g) ≤ 0.001384552127 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12663 12663 0.011
      (momentAllowance 12663 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12663 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12663 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12663 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12663 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12663 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229742522982 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12663 0.011
      (momentAllowance 12663 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12663 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12663
/-! The actual computed-centre upper energy formula at 12663. -/
namespace BstLean.Part269.N12663
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12663

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12663
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12663)
open BstLean.Part268 (cell12663)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085598910450
  | 2 => 0.086543673068
  | 3 => 0.087486871786
  | 4 => 0.088429992762
  | 5 => 0.089374831305
  | 6 => 0.090323537493
  | 7 => 0.091278666033
  | 8 => 0.092243230388
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12663 12663 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12663 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12663

/-! Actual upper energy certificates on all 43 source endpoints at 12663. -/
namespace BstLean.Part269.N12663
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12663)
open BstLean.Part268 (cell12663)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12663 (gMinus 12663) (1 - (cell12663 i).lower) ≤ 1 ∧
    energyUpper 12663 (gMinus 12663) (BstLean.Part211.gPlus 12663)
      (finiteEnergy 12663 12663 0.011) (1 - (cell12663 i).lower) ≤
      (cell12663 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨10,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨11,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨12,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨13,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨14,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨15,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨16,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨17,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨18,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨19,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨20,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨21,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨22,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨23,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨24,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨25,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨26,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨27,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨28,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨29,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨30,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨31,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨32,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨33,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨34,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨35,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨36,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨37,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨38,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨39,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨40,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨41,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨42,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨43,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨44,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨45,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨46,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨47,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨48,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨49,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨50,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨51,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12663) (by norm_num)
        (q := 1 - (cell12663 ⟨52,by decide⟩).lower)
        (by norm_num [cell12663]) (by norm_num [cell12663])
      exact ⟨E.1,E.2.trans (by norm_num [cell12663])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12663

/-! Source-cell containment and simple scalar guards at 12663. -/
namespace BstLean.Part269.N12663
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12663)
open BstLean.Part268 (cell12663)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12663 ⟨10,by decide⟩).lower ∧ (cell12663 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12663 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12663 ⟨11,by decide⟩).lower ∧ (cell12663 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12663 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12663 ⟨12,by decide⟩).lower ∧ (cell12663 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12663 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12663 ⟨13,by decide⟩).lower ∧ (cell12663 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12663 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12663 ⟨14,by decide⟩).lower ∧ (cell12663 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12663 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12663 ⟨15,by decide⟩).lower ∧ (cell12663 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12663 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12663 ⟨16,by decide⟩).lower ∧ (cell12663 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12663 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12663 ⟨17,by decide⟩).lower ∧ (cell12663 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12663 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12663 ⟨18,by decide⟩).lower ∧ (cell12663 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12663 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12663 ⟨19,by decide⟩).lower ∧ (cell12663 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12663 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12663 ⟨20,by decide⟩).lower ∧ (cell12663 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12663 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12663 ⟨21,by decide⟩).lower ∧ (cell12663 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12663 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12663 ⟨22,by decide⟩).lower ∧ (cell12663 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12663 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12663 ⟨23,by decide⟩).lower ∧ (cell12663 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12663 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12663 ⟨24,by decide⟩).lower ∧ (cell12663 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12663 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12663 ⟨25,by decide⟩).lower ∧ (cell12663 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12663 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12663 ⟨26,by decide⟩).lower ∧ (cell12663 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12663 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12663 ⟨27,by decide⟩).lower ∧ (cell12663 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12663 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12663 ⟨28,by decide⟩).lower ∧ (cell12663 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12663 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12663 ⟨29,by decide⟩).lower ∧ (cell12663 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12663 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12663 ⟨30,by decide⟩).lower ∧ (cell12663 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12663 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12663 ⟨31,by decide⟩).lower ∧ (cell12663 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12663 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12663 ⟨32,by decide⟩).lower ∧ (cell12663 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12663 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12663 ⟨33,by decide⟩).lower ∧ (cell12663 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12663 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12663 ⟨34,by decide⟩).lower ∧ (cell12663 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12663 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12663 ⟨35,by decide⟩).lower ∧ (cell12663 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12663 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12663 ⟨36,by decide⟩).lower ∧ (cell12663 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12663 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12663 ⟨37,by decide⟩).lower ∧ (cell12663 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12663 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12663 ⟨38,by decide⟩).lower ∧ (cell12663 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12663 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12663 ⟨39,by decide⟩).lower ∧ (cell12663 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12663 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12663 ⟨40,by decide⟩).lower ∧ (cell12663 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12663 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12663 ⟨41,by decide⟩).lower ∧ (cell12663 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12663 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12663 ⟨42,by decide⟩).lower ∧ (cell12663 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12663 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12663 ⟨43,by decide⟩).lower ∧ (cell12663 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12663 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12663 ⟨44,by decide⟩).lower ∧ (cell12663 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12663 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12663 ⟨45,by decide⟩).lower ∧ (cell12663 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12663 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12663 ⟨46,by decide⟩).lower ∧ (cell12663 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12663 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12663 ⟨47,by decide⟩).lower ∧ (cell12663 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12663 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12663 ⟨48,by decide⟩).lower ∧ (cell12663 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12663 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12663 ⟨49,by decide⟩).lower ∧ (cell12663 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12663 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12663 ⟨50,by decide⟩).lower ∧ (cell12663 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12663 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12663 ⟨51,by decide⟩).lower ∧ (cell12663 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12663 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12663 ⟨52,by decide⟩).lower ∧ (cell12663 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12663 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12663 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12663 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12663,cell12663,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12663 i).lower ∧
    (cell12663 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12663 i).upper ≤ (0.532 : ℝ) ∧
    (cell12663 i).centre ≤ (0.1 : ℝ) ∧ (cell12663 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12663 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12663 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12663

/-! The local source numeric instances at 12663 have no network premises. -/
namespace BstLean.Part269.N12663
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12663)
open BstLean.Part268 (cell12663)

noncomputable def sourceNumerics12663 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12663 (cell12663 i)
      scalarRow12663.M scalarRow12663.H scalarRow12663.xi := by
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
    energy_allowance := scalarRow12663.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12663]
    centre_nonneg := (scalarRow12663.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12663])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12663
/-! Actual 12664 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12664
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12664 ≤ (1.035860530377 : ℝ) := by
  have hr : (112.534439173081 : ℝ) ≤ √(12664 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.534439173081 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12664 12664 (11 / 1000) ≤
    (0.008494173398 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12664) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.534439173081 : ℝ) ≤ √(12664 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12664)
  have hdiv : K / √(12664 : ℝ) ≤ K / 112.534439173081 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.534439173081 ≤ (0.008494173398 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12664.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12664 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12664 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12664 := gPlus_lower 12664
end BstLean.Part269.N12664

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12664
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035860530376 : ℝ) ≤ wn 12664 := by
  have hn : √(12664 : ℝ) ≤ 112.534439173082 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12664 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.534439173082 ≤ 2 / √(12664 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252609404 : ℝ) ≤ rhoBar 12664 BstLean.Part154.csC ∧
    rhoBar 12664 BstLean.Part154.csC ≤ 0.000252609795 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035860530376 : ℝ) / (1.295212 * 12664) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035860530377 : ℝ) / (1.29521 * 12664) := by gcongr
      _ ≤ (0.000252609795 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12664 BstLean.Part154.csC) ≤ 0.001010502992 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12664 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12664 BstLean.Part154.csC) (piBar (rhoBar 12664 BstLean.Part154.csC)) ≤ 0.000192945091 ∧
    cc1 (rhoBar 12664 BstLean.Part154.csC) (piBar (rhoBar 12664 BstLean.Part154.csC)) ≤ 0.000122772237 ∧
    cc2 (rhoBar 12664 BstLean.Part154.csC) ≤ 0.000071270218 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12664 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12664 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12664 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12664 BstLean.Part154.csC * nuR (rhoBar 12664 BstLean.Part154.csC)) ≤ 0.000505235543 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252609795 : ℝ) * 0.001010502992 := by gcongr
      _ ≤ (0.000505235543 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12664 BstLean.Part154.csC) * nuR (rhoBar 12664 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001010502992 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12664 BstLean.Part154.csC) * rhoBar 12664 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252609795 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252609795 / 2 + 0.399 * 0.001010502992 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192945091 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505235543 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122772237 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252609795 / 1.414213562 := by gcongr
      _ ≤ (0.000071270218 : ℝ) := by norm_num

end BstLean.Part269.N12664

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12664
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12664 BstLean.Part154.csC) (piBar (rhoBar 12664 BstLean.Part154.csC)) ≤ 1.60769E-7 := by
  have hr0 : 0 ≤ rhoBar 12664 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12664 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12664 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12664 BstLean.Part154.csC) (piBar (rhoBar 12664 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12664 BstLean.Part154.csC) (piBar (rhoBar 12664 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12664 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192945091 : ℝ) ^ 2 + 0.000122772237 ^ 2 + 3 * 0.000071270218 ^ 2 +
        2 * 0.797885 * 0.000192945091 * 0.000122772237 + 2 * 0.000192945091 * 0.000071270218 +
        4 * 0.797885 * 0.000122772237 * 0.000071270218 := by gcongr
    _ ≤ (1.60769E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12664 BstLean.Part154.csC Θ ≤ 0.002637023943 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12664 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12664 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12664 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12664 BstLean.Part154.csC) (piBar (rhoBar 12664 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12664 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035860530377 * 1.60769E-7 / (0.000252609404 : ℝ) := by gcongr
    _ ≤ 0.002637023943 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12664 BstLean.Part154.csC Θ ≤ 0.002926066455 + 0.000666333544 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12664 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12664 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12664 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035860530377 : ℝ) * ((2 * Θ * 0.000252609795 +
        (6863 / 10000) * 0.000252609795 * 12664 * 0.001010502992) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002926066455 + 0.000666333544 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12664 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12664 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12664 0.011 Θ ∧ gammaRatio 12664 0.011 Θ ≤ 0.000086840716 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12664 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035860530377 : ℝ) * 0.525 / ((1 - 0.011) * 12664) := by gcongr
      _ ≤ (0.000086840716 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12664 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12664 0.011 Θ) :=
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
    badAllowance 12664 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12664 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12664 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12664 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12664 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12664 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12664 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12664 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12664 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12664 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12664 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035860530377 : ℝ) * 12664 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12664 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003540377846 + 0.003303357487 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12664

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12664
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12664 BstLean.Part154.csC) (piBar (rhoBar 12664 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12664 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12664 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12664 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12664 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12664 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12664 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12664 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12664 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12664 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12664 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12664 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12664 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12664 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12664 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052559668013 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12664) ≤ 0.010612196496 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12664 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035860530377)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010612196496 + 2 * 0.737676 / 12664) := by gcongr
    _ ≤ (0.052559668013 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12664 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12664

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12664
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501935636 : ℝ) ≤ plow 12664 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12664) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052781240527)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384437571) : eMP 12664 0.011 xi bn ≤ 0.001191816452 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12664 : ℝ) * (1 - 0.011))) ≤ 0.000589288617 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001384437571 / (12664 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589288617 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589288617 : ℝ) + 3.141593 * 0.052781240527 / (12664 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001191816452 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052781240527)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384437571) : PiBarMP 12664 12 0.011 xi bn ≤ 0.161482182654 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12664 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037208031002 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.913788247918 : ℝ) ≤ √((12664 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.534439173081 : ℝ) ≤ √(12664 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12664) ≤ 0.123805728852 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037208031002 + 0.052781240527 * 1.772454 / (2 * (111.913788247918 : ℝ))) * (1 + 0.001191816452) +
        8 / (12664 * 112.534439173081) + 0.123805728852 := by gcongr
    _ ≤ (0.161482182654 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052781240527)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384437571) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282301350185) :
    parallelOracle 12664 0.011 xi bn cd ≤ 0.162475279438 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12664 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12664 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501935636 : ℝ) ≤ plow 12664 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.534439173081 : ℝ) ≤ √(12664 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282301350185 : ℝ) / (2 * 0.560501935636 * 112.534439173081)) * 0.161482182654 +
        0.282301350185 ^ 2 / (2 * 0.560501935636 * 112.534439173081) := by gcongr
    _ ≤ (0.162475279438 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052781240527) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384437571)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282301350185) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12664 12664 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501935636 : ℝ) ≤ plow 12664 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.534439173081 : ℝ) ≤ √(12664 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12664 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12664 Θ 1.22 ≤ 0.011783952626 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.534439173081 := by gcongr <;> linarith
      _ ≤ (0.011783952626 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12664 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12664 12664 0.011 ≤ 0.008494173398 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12664 12664 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12664 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12664 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12664 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12664 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162475279438 + 0.011783952626 + (0.008494173398 : ℝ) *
        (1 + 2 * (0.282301350185 + 0.011783952626) / (0.560501935636 * 112.534439173081))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12664]

end BstLean.Part269.N12664

/-! The original eight local profiles supply actual 12664 moment certificates. -/
namespace BstLean.Part269.N12664
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12664 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12664 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12664 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052781240527 ∧
    0 ≤ bN 12664 BstLean.Part154.csC (groupTheta g) ∧ bN 12664 BstLean.Part154.csC (groupTheta g) ≤ 0.001384437571 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12664 12664 0.011
      (momentAllowance 12664 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12664 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12664 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12664 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12664 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12664 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229741682172 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12664 0.011
      (momentAllowance 12664 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12664 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12664
/-! The actual computed-centre upper energy formula at 12664. -/
namespace BstLean.Part269.N12664
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12664

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12664
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12664)
open BstLean.Part268 (cell12664)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085595953849
  | 2 => 0.086540661225
  | 3 => 0.087483796494
  | 4 => 0.088426843935
  | 5 => 0.089371596647
  | 6 => 0.090320202126
  | 7 => 0.091275212086
  | 8 => 0.092239636537
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12664 12664 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12664 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12664

/-! Actual upper energy certificates on all 43 source endpoints at 12664. -/
namespace BstLean.Part269.N12664
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12664)
open BstLean.Part268 (cell12664)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12664 (gMinus 12664) (1 - (cell12664 i).lower) ≤ 1 ∧
    energyUpper 12664 (gMinus 12664) (BstLean.Part211.gPlus 12664)
      (finiteEnergy 12664 12664 0.011) (1 - (cell12664 i).lower) ≤
      (cell12664 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨10,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨11,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨12,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨13,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨14,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨15,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨16,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨17,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨18,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨19,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨20,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨21,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨22,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨23,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨24,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨25,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨26,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨27,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨28,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨29,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨30,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨31,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨32,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨33,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨34,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨35,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨36,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨37,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨38,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨39,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨40,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨41,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨42,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨43,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨44,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨45,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨46,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨47,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨48,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨49,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨50,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨51,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12664) (by norm_num)
        (q := 1 - (cell12664 ⟨52,by decide⟩).lower)
        (by norm_num [cell12664]) (by norm_num [cell12664])
      exact ⟨E.1,E.2.trans (by norm_num [cell12664])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12664

/-! Source-cell containment and simple scalar guards at 12664. -/
namespace BstLean.Part269.N12664
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12664)
open BstLean.Part268 (cell12664)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12664 ⟨10,by decide⟩).lower ∧ (cell12664 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12664 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12664 ⟨11,by decide⟩).lower ∧ (cell12664 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12664 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12664 ⟨12,by decide⟩).lower ∧ (cell12664 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12664 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12664 ⟨13,by decide⟩).lower ∧ (cell12664 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12664 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12664 ⟨14,by decide⟩).lower ∧ (cell12664 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12664 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12664 ⟨15,by decide⟩).lower ∧ (cell12664 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12664 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12664 ⟨16,by decide⟩).lower ∧ (cell12664 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12664 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12664 ⟨17,by decide⟩).lower ∧ (cell12664 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12664 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12664 ⟨18,by decide⟩).lower ∧ (cell12664 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12664 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12664 ⟨19,by decide⟩).lower ∧ (cell12664 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12664 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12664 ⟨20,by decide⟩).lower ∧ (cell12664 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12664 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12664 ⟨21,by decide⟩).lower ∧ (cell12664 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12664 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12664 ⟨22,by decide⟩).lower ∧ (cell12664 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12664 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12664 ⟨23,by decide⟩).lower ∧ (cell12664 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12664 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12664 ⟨24,by decide⟩).lower ∧ (cell12664 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12664 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12664 ⟨25,by decide⟩).lower ∧ (cell12664 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12664 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12664 ⟨26,by decide⟩).lower ∧ (cell12664 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12664 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12664 ⟨27,by decide⟩).lower ∧ (cell12664 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12664 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12664 ⟨28,by decide⟩).lower ∧ (cell12664 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12664 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12664 ⟨29,by decide⟩).lower ∧ (cell12664 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12664 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12664 ⟨30,by decide⟩).lower ∧ (cell12664 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12664 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12664 ⟨31,by decide⟩).lower ∧ (cell12664 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12664 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12664 ⟨32,by decide⟩).lower ∧ (cell12664 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12664 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12664 ⟨33,by decide⟩).lower ∧ (cell12664 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12664 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12664 ⟨34,by decide⟩).lower ∧ (cell12664 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12664 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12664 ⟨35,by decide⟩).lower ∧ (cell12664 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12664 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12664 ⟨36,by decide⟩).lower ∧ (cell12664 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12664 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12664 ⟨37,by decide⟩).lower ∧ (cell12664 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12664 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12664 ⟨38,by decide⟩).lower ∧ (cell12664 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12664 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12664 ⟨39,by decide⟩).lower ∧ (cell12664 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12664 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12664 ⟨40,by decide⟩).lower ∧ (cell12664 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12664 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12664 ⟨41,by decide⟩).lower ∧ (cell12664 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12664 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12664 ⟨42,by decide⟩).lower ∧ (cell12664 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12664 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12664 ⟨43,by decide⟩).lower ∧ (cell12664 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12664 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12664 ⟨44,by decide⟩).lower ∧ (cell12664 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12664 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12664 ⟨45,by decide⟩).lower ∧ (cell12664 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12664 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12664 ⟨46,by decide⟩).lower ∧ (cell12664 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12664 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12664 ⟨47,by decide⟩).lower ∧ (cell12664 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12664 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12664 ⟨48,by decide⟩).lower ∧ (cell12664 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12664 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12664 ⟨49,by decide⟩).lower ∧ (cell12664 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12664 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12664 ⟨50,by decide⟩).lower ∧ (cell12664 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12664 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12664 ⟨51,by decide⟩).lower ∧ (cell12664 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12664 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12664 ⟨52,by decide⟩).lower ∧ (cell12664 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12664 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12664 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12664 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12664,cell12664,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12664 i).lower ∧
    (cell12664 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12664 i).upper ≤ (0.532 : ℝ) ∧
    (cell12664 i).centre ≤ (0.1 : ℝ) ∧ (cell12664 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12664 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12664 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12664

/-! The local source numeric instances at 12664 have no network premises. -/
namespace BstLean.Part269.N12664
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12664)
open BstLean.Part268 (cell12664)

noncomputable def sourceNumerics12664 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12664 (cell12664 i)
      scalarRow12664.M scalarRow12664.H scalarRow12664.xi := by
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
    energy_allowance := scalarRow12664.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12664]
    centre_nonneg := (scalarRow12664.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12664])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12664
/-! Actual 12665 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12665
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12665 ≤ (1.035859102146 : ℝ) := by
  have hr : (112.538882169675 : ℝ) ≤ √(12665 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.538882169675 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12665 12665 (11 / 1000) ≤
    (0.008493838048 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12665) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.538882169675 : ℝ) ≤ √(12665 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12665)
  have hdiv : K / √(12665 : ℝ) ≤ K / 112.538882169675 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.538882169675 ≤ (0.008493838048 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12665.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12665 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12665 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12665 := gPlus_lower 12665
end BstLean.Part269.N12665

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12665
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035859102145 : ℝ) ≤ wn 12665 := by
  have hn : √(12665 : ℝ) ≤ 112.538882169676 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12665 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.538882169676 ≤ 2 / √(12665 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252589110 : ℝ) ≤ rhoBar 12665 BstLean.Part154.csC ∧
    rhoBar 12665 BstLean.Part154.csC ≤ 0.000252589501 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035859102145 : ℝ) / (1.295212 * 12665) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035859102146 : ℝ) / (1.29521 * 12665) := by gcongr
      _ ≤ (0.000252589501 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12665 BstLean.Part154.csC) ≤ 0.001010421806 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12665 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12665 BstLean.Part154.csC) (piBar (rhoBar 12665 BstLean.Part154.csC)) ≤ 0.000192929590 ∧
    cc1 (rhoBar 12665 BstLean.Part154.csC) (piBar (rhoBar 12665 BstLean.Part154.csC)) ≤ 0.000122762374 ∧
    cc2 (rhoBar 12665 BstLean.Part154.csC) ≤ 0.000071264492 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12665 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12665 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12665 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12665 BstLean.Part154.csC * nuR (rhoBar 12665 BstLean.Part154.csC)) ≤ 0.000505194953 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252589501 : ℝ) * 0.001010421806 := by gcongr
      _ ≤ (0.000505194953 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12665 BstLean.Part154.csC) * nuR (rhoBar 12665 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001010421806 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12665 BstLean.Part154.csC) * rhoBar 12665 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252589501 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252589501 / 2 + 0.399 * 0.001010421806 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192929590 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505194953 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122762374 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252589501 / 1.414213562 := by gcongr
      _ ≤ (0.000071264492 : ℝ) := by norm_num

end BstLean.Part269.N12665

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12665
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12665 BstLean.Part154.csC) (piBar (rhoBar 12665 BstLean.Part154.csC)) ≤ 1.60743E-7 := by
  have hr0 : 0 ≤ rhoBar 12665 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12665 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12665 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12665 BstLean.Part154.csC) (piBar (rhoBar 12665 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12665 BstLean.Part154.csC) (piBar (rhoBar 12665 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12665 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192929590 : ℝ) ^ 2 + 0.000122762374 ^ 2 + 3 * 0.000071264492 ^ 2 +
        2 * 0.797885 * 0.000192929590 * 0.000122762374 + 2 * 0.000192929590 * 0.000071264492 +
        4 * 0.797885 * 0.000122762374 * 0.000071264492 := by gcongr
    _ ≤ (1.60743E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12665 BstLean.Part154.csC Θ ≤ 0.002636805675 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12665 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12665 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12665 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12665 BstLean.Part154.csC) (piBar (rhoBar 12665 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12665 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035859102146 * 1.60743E-7 / (0.000252589110 : ℝ) := by gcongr
    _ ≤ 0.002636805675 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12665 BstLean.Part154.csC Θ ≤ 0.002925823298 + 0.000666279094 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12665 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12665 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12665 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035859102146 : ℝ) * ((2 * Θ * 0.000252589501 +
        (6863 / 10000) * 0.000252589501 * 12665 * 0.001010421806) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002925823298 + 0.000666279094 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12665 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12665 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12665 0.011 Θ ∧ gammaRatio 12665 0.011 Θ ≤ 0.000086833739 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12665 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035859102146 : ℝ) * 0.525 / ((1 - 0.011) * 12665) := by gcongr
      _ ≤ (0.000086833739 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12665 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12665 0.011 Θ) :=
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
    badAllowance 12665 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12665 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12665 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12665 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12665 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12665 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12665 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12665 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12665 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12665 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12665 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035859102146 : ℝ) * 12665 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12665 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003540134689 + 0.003303084769 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12665

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12665
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12665 BstLean.Part154.csC) (piBar (rhoBar 12665 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12665 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12665 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12665 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12665 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12665 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12665 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12665 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12665 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12665 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12665 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12665 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12665 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12665 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12665 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052557570444 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12665) ≤ 0.010611777530 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12665 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035859102146)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010611777530 + 2 * 0.737676 / 12665) := by gcongr
    _ ≤ (0.052557570444 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12665 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12665

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12665
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560501981113 : ℝ) ≤ plow 12665 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12665) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052780854193)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384322980) : eMP 12665 0.011 xi bn ≤ 0.001191720006 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12665 : ℝ) * (1 - 0.011))) ≤ 0.000589240965 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001384322980 / (12665 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589240965 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589240965 : ℝ) + 3.141593 * 0.052780854193 / (12665 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001191720006 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052780854193)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384322980) : PiBarMP 12665 12 0.011 xi bn ≤ 0.161475729232 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12665 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037206491101 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.918206740458 : ℝ) ≤ √((12665 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.538882169675 : ℝ) ≤ √(12665 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12665) ≤ 0.123800841044 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037206491101 + 0.052780854193 * 1.772454 / (2 * (111.918206740458 : ℝ))) * (1 + 0.001191720006) +
        8 / (12665 * 112.538882169675) + 0.123800841044 := by gcongr
    _ ≤ (0.161475729232 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052780854193)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384322980) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282298411814) :
    parallelOracle 12665 0.011 xi bn cd ≤ 0.162468755376 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12665 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12665 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560501981113 : ℝ) ≤ plow 12665 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.538882169675 : ℝ) ≤ √(12665 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282298411814 : ℝ) / (2 * 0.560501981113 * 112.538882169675)) * 0.161475729232 +
        0.282298411814 ^ 2 / (2 * 0.560501981113 * 112.538882169675) := by gcongr
    _ ≤ (0.162468755376 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052780854193) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384322980)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282298411814) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12665 12665 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560501981113 : ℝ) ≤ plow 12665 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.538882169675 : ℝ) ≤ √(12665 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12665 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12665 Θ 1.22 ≤ 0.011783487400 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.538882169675 := by gcongr <;> linarith
      _ ≤ (0.011783487400 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12665 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12665 12665 0.011 ≤ 0.008493838048 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12665 12665 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12665 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12665 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12665 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12665 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162468755376 + 0.011783487400 + (0.008493838048 : ℝ) *
        (1 + 2 * (0.282298411814 + 0.011783487400) / (0.560501981113 * 112.538882169675))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12665]

end BstLean.Part269.N12665

/-! The original eight local profiles supply actual 12665 moment certificates. -/
namespace BstLean.Part269.N12665
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12665 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12665 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12665 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052780854193 ∧
    0 ≤ bN 12665 BstLean.Part154.csC (groupTheta g) ∧ bN 12665 BstLean.Part154.csC (groupTheta g) ≤ 0.001384322980 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12665 12665 0.011
      (momentAllowance 12665 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12665 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12665 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12665 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12665 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12665 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229740841370 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12665 0.011
      (momentAllowance 12665 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12665 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12665
/-! The actual computed-centre upper energy formula at 12665. -/
namespace BstLean.Part269.N12665
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12665

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12665
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12665)
open BstLean.Part268 (cell12665)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085592998372
  | 2 => 0.086537650553
  | 3 => 0.087480722431
  | 4 => 0.088423696408
  | 5 => 0.089368363374
  | 6 => 0.090316868250
  | 7 => 0.091271759756
  | 8 => 0.092236044456
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12665 12665 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12665 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12665

/-! Actual upper energy certificates on all 43 source endpoints at 12665. -/
namespace BstLean.Part269.N12665
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12665)
open BstLean.Part268 (cell12665)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12665 (gMinus 12665) (1 - (cell12665 i).lower) ≤ 1 ∧
    energyUpper 12665 (gMinus 12665) (BstLean.Part211.gPlus 12665)
      (finiteEnergy 12665 12665 0.011) (1 - (cell12665 i).lower) ≤
      (cell12665 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨10,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨11,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨12,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨13,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨14,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨15,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨16,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨17,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨18,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨19,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨20,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨21,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨22,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨23,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨24,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨25,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨26,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨27,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨28,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨29,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨30,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨31,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨32,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨33,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨34,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨35,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨36,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨37,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨38,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨39,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨40,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨41,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨42,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨43,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨44,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨45,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨46,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨47,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨48,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨49,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨50,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨51,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12665) (by norm_num)
        (q := 1 - (cell12665 ⟨52,by decide⟩).lower)
        (by norm_num [cell12665]) (by norm_num [cell12665])
      exact ⟨E.1,E.2.trans (by norm_num [cell12665])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12665

/-! Source-cell containment and simple scalar guards at 12665. -/
namespace BstLean.Part269.N12665
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12665)
open BstLean.Part268 (cell12665)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12665 ⟨10,by decide⟩).lower ∧ (cell12665 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12665 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12665 ⟨11,by decide⟩).lower ∧ (cell12665 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12665 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12665 ⟨12,by decide⟩).lower ∧ (cell12665 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12665 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12665 ⟨13,by decide⟩).lower ∧ (cell12665 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12665 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12665 ⟨14,by decide⟩).lower ∧ (cell12665 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12665 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12665 ⟨15,by decide⟩).lower ∧ (cell12665 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12665 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12665 ⟨16,by decide⟩).lower ∧ (cell12665 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12665 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12665 ⟨17,by decide⟩).lower ∧ (cell12665 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12665 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12665 ⟨18,by decide⟩).lower ∧ (cell12665 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12665 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12665 ⟨19,by decide⟩).lower ∧ (cell12665 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12665 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12665 ⟨20,by decide⟩).lower ∧ (cell12665 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12665 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12665 ⟨21,by decide⟩).lower ∧ (cell12665 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12665 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12665 ⟨22,by decide⟩).lower ∧ (cell12665 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12665 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12665 ⟨23,by decide⟩).lower ∧ (cell12665 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12665 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12665 ⟨24,by decide⟩).lower ∧ (cell12665 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12665 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12665 ⟨25,by decide⟩).lower ∧ (cell12665 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12665 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12665 ⟨26,by decide⟩).lower ∧ (cell12665 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12665 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12665 ⟨27,by decide⟩).lower ∧ (cell12665 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12665 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12665 ⟨28,by decide⟩).lower ∧ (cell12665 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12665 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12665 ⟨29,by decide⟩).lower ∧ (cell12665 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12665 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12665 ⟨30,by decide⟩).lower ∧ (cell12665 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12665 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12665 ⟨31,by decide⟩).lower ∧ (cell12665 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12665 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12665 ⟨32,by decide⟩).lower ∧ (cell12665 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12665 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12665 ⟨33,by decide⟩).lower ∧ (cell12665 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12665 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12665 ⟨34,by decide⟩).lower ∧ (cell12665 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12665 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12665 ⟨35,by decide⟩).lower ∧ (cell12665 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12665 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12665 ⟨36,by decide⟩).lower ∧ (cell12665 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12665 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12665 ⟨37,by decide⟩).lower ∧ (cell12665 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12665 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12665 ⟨38,by decide⟩).lower ∧ (cell12665 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12665 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12665 ⟨39,by decide⟩).lower ∧ (cell12665 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12665 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12665 ⟨40,by decide⟩).lower ∧ (cell12665 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12665 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12665 ⟨41,by decide⟩).lower ∧ (cell12665 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12665 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12665 ⟨42,by decide⟩).lower ∧ (cell12665 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12665 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12665 ⟨43,by decide⟩).lower ∧ (cell12665 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12665 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12665 ⟨44,by decide⟩).lower ∧ (cell12665 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12665 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12665 ⟨45,by decide⟩).lower ∧ (cell12665 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12665 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12665 ⟨46,by decide⟩).lower ∧ (cell12665 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12665 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12665 ⟨47,by decide⟩).lower ∧ (cell12665 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12665 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12665 ⟨48,by decide⟩).lower ∧ (cell12665 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12665 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12665 ⟨49,by decide⟩).lower ∧ (cell12665 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12665 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12665 ⟨50,by decide⟩).lower ∧ (cell12665 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12665 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12665 ⟨51,by decide⟩).lower ∧ (cell12665 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12665 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12665 ⟨52,by decide⟩).lower ∧ (cell12665 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12665 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12665 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12665 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12665,cell12665,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12665 i).lower ∧
    (cell12665 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12665 i).upper ≤ (0.532 : ℝ) ∧
    (cell12665 i).centre ≤ (0.1 : ℝ) ∧ (cell12665 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12665 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12665 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12665

/-! The local source numeric instances at 12665 have no network premises. -/
namespace BstLean.Part269.N12665
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12665)
open BstLean.Part268 (cell12665)

noncomputable def sourceNumerics12665 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12665 (cell12665 i)
      scalarRow12665.M scalarRow12665.H scalarRow12665.xi := by
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
    energy_allowance := scalarRow12665.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12665]
    centre_nonneg := (scalarRow12665.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12665])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12665
/-! Actual 12666 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12666
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12666 ≤ (1.035857674086 : ℝ) := by
  have hr : (112.543324990867 : ℝ) ≤ √(12666 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.543324990867 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12666 12666 (11 / 1000) ≤
    (0.008493502738 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12666) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.543324990867 : ℝ) ≤ √(12666 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12666)
  have hdiv : K / √(12666 : ℝ) ≤ K / 112.543324990867 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.543324990867 ≤ (0.008493502738 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12666.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12666 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12666 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12666 := gPlus_lower 12666
end BstLean.Part269.N12666

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12666
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035857674085 : ℝ) ≤ wn 12666 := by
  have hn : √(12666 : ℝ) ≤ 112.543324990868 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12666 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.543324990868 ≤ 2 / √(12666 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252568820 : ℝ) ≤ rhoBar 12666 BstLean.Part154.csC ∧
    rhoBar 12666 BstLean.Part154.csC ≤ 0.000252569211 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035857674085 : ℝ) / (1.295212 * 12666) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035857674086 : ℝ) / (1.29521 * 12666) := by gcongr
      _ ≤ (0.000252569211 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12666 BstLean.Part154.csC) ≤ 0.001010340636 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12666 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12666 BstLean.Part154.csC) (piBar (rhoBar 12666 BstLean.Part154.csC)) ≤ 0.000192914092 ∧
    cc1 (rhoBar 12666 BstLean.Part154.csC) (piBar (rhoBar 12666 BstLean.Part154.csC)) ≤ 0.000122752512 ∧
    cc2 (rhoBar 12666 BstLean.Part154.csC) ≤ 0.000071258768 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12666 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12666 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12666 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12666 BstLean.Part154.csC * nuR (rhoBar 12666 BstLean.Part154.csC)) ≤ 0.000505154370 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252569211 : ℝ) * 0.001010340636 := by gcongr
      _ ≤ (0.000505154370 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12666 BstLean.Part154.csC) * nuR (rhoBar 12666 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001010340636 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12666 BstLean.Part154.csC) * rhoBar 12666 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252569211 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252569211 / 2 + 0.399 * 0.001010340636 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192914092 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505154370 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122752512 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252569211 / 1.414213562 := by gcongr
      _ ≤ (0.000071258768 : ℝ) := by norm_num

end BstLean.Part269.N12666

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12666
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12666 BstLean.Part154.csC) (piBar (rhoBar 12666 BstLean.Part154.csC)) ≤ 1.60718E-7 := by
  have hr0 : 0 ≤ rhoBar 12666 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12666 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12666 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12666 BstLean.Part154.csC) (piBar (rhoBar 12666 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12666 BstLean.Part154.csC) (piBar (rhoBar 12666 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12666 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192914092 : ℝ) ^ 2 + 0.000122752512 ^ 2 + 3 * 0.000071258768 ^ 2 +
        2 * 0.797885 * 0.000192914092 * 0.000122752512 + 2 * 0.000192914092 * 0.000071258768 +
        4 * 0.797885 * 0.000122752512 * 0.000071258768 := by gcongr
    _ ≤ (1.60718E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12666 BstLean.Part154.csC Θ ≤ 0.002636603737 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12666 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12666 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12666 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12666 BstLean.Part154.csC) (piBar (rhoBar 12666 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12666 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035857674086 * 1.60718E-7 / (0.000252568820 : ℝ) := by gcongr
    _ ≤ 0.002636603737 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12666 BstLean.Part154.csC Θ ≤ 0.002925580198 + 0.000666224655 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12666 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12666 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12666 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035857674086 : ℝ) * ((2 * Θ * 0.000252569211 +
        (6863 / 10000) * 0.000252569211 * 12666 * 0.001010340636) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002925580198 + 0.000666224655 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12666 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12666 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12666 0.011 Θ ∧ gammaRatio 12666 0.011 Θ ≤ 0.000086826764 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12666 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035857674086 : ℝ) * 0.525 / ((1 - 0.011) * 12666) := by gcongr
      _ ≤ (0.000086826764 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12666 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12666 0.011 Θ) :=
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
    badAllowance 12666 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12666 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12666 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12666 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12666 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12666 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12666 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12666 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12666 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12666 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12666 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035857674086 : ℝ) * 12666 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12666 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003539891589 + 0.003302828392 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12666

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12666
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12666 BstLean.Part154.csC) (piBar (rhoBar 12666 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12666 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12666 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12666 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12666 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12666 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12666 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12666 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12666 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12666 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12666 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12666 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12666 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12666 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12666 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052555473126 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12666) ≤ 0.010611358614 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12666 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035857674086)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010611358614 + 2 * 0.737676 / 12666) := by gcongr
    _ ≤ (0.052555473126 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12666 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12666

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12666
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502026582 : ℝ) ≤ plow 12666 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12666) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052780476495)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384216962) : eMP 12666 0.011 xi bn ≤ 0.001191627218 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12666 : ℝ) * (1 - 0.011))) ≤ 0.000589195141 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001384216962 / (12666 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589195141 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589195141 : ℝ) + 3.141593 * 0.052780476495 / (12666 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001191627218 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052780476495)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384216962) : PiBarMP 12666 12 0.011 xi bn ≤ 0.161469391885 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12666 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037205066349 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.922625058564 : ℝ) ≤ √((12666 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.543324990867 : ℝ) ≤ √(12666 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12666) ≤ 0.123795953815 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037205066349 + 0.052780476495 * 1.772454 / (2 * (111.922625058564 : ℝ))) * (1 + 0.001191627218) +
        8 / (12666 * 112.543324990867) + 0.123795953815 := by gcongr
    _ ≤ (0.161469391885 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052780476495)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384216962) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282295492485) :
    parallelOracle 12666 0.011 xi bn cd ≤ 0.162462347766 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12666 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12666 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502026582 : ℝ) ≤ plow 12666 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.543324990867 : ℝ) ≤ √(12666 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282295492485 : ℝ) / (2 * 0.560502026582 * 112.543324990867)) * 0.161469391885 +
        0.282295492485 ^ 2 / (2 * 0.560502026582 * 112.543324990867) := by gcongr
    _ ≤ (0.162462347766 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052780476495) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384216962)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282295492485) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12666 12666 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502026582 : ℝ) ≤ plow 12666 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.543324990867 : ℝ) ≤ √(12666 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12666 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12666 Θ 1.22 ≤ 0.011783022229 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.543324990867 := by gcongr <;> linarith
      _ ≤ (0.011783022229 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12666 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12666 12666 0.011 ≤ 0.008493502738 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12666 12666 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12666 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12666 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12666 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12666 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162462347766 + 0.011783022229 + (0.008493502738 : ℝ) *
        (1 + 2 * (0.282295492485 + 0.011783022229) / (0.560502026582 * 112.543324990867))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12666]

end BstLean.Part269.N12666

/-! The original eight local profiles supply actual 12666 moment certificates. -/
namespace BstLean.Part269.N12666
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12666 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12666 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12666 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052780476495 ∧
    0 ≤ bN 12666 BstLean.Part154.csC (groupTheta g) ∧ bN 12666 BstLean.Part154.csC (groupTheta g) ≤ 0.001384216962 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12666 12666 0.011
      (momentAllowance 12666 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12666 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12666 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12666 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12666 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12666 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229740019359 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12666 0.011
      (momentAllowance 12666 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12666 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12666
/-! The actual computed-centre upper energy formula at 12666. -/
namespace BstLean.Part269.N12666
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12666

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12666
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12666)
open BstLean.Part268 (cell12666)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085590044018
  | 2 => 0.086534641051
  | 3 => 0.087477649596
  | 4 => 0.088420550179
  | 5 => 0.089365131486
  | 6 => 0.090313535862
  | 7 => 0.091268309043
  | 8 => 0.092232454145
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12666 12666 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12666 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12666

/-! Actual upper energy certificates on all 43 source endpoints at 12666. -/
namespace BstLean.Part269.N12666
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12666)
open BstLean.Part268 (cell12666)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12666 (gMinus 12666) (1 - (cell12666 i).lower) ≤ 1 ∧
    energyUpper 12666 (gMinus 12666) (BstLean.Part211.gPlus 12666)
      (finiteEnergy 12666 12666 0.011) (1 - (cell12666 i).lower) ≤
      (cell12666 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨10,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨11,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨12,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨13,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨14,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨15,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨16,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨17,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨18,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨19,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨20,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨21,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨22,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨23,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨24,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨25,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨26,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨27,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨28,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨29,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨30,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨31,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨32,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨33,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨34,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨35,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨36,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨37,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨38,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨39,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨40,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨41,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨42,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨43,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨44,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨45,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨46,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨47,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨48,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨49,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨50,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨51,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12666) (by norm_num)
        (q := 1 - (cell12666 ⟨52,by decide⟩).lower)
        (by norm_num [cell12666]) (by norm_num [cell12666])
      exact ⟨E.1,E.2.trans (by norm_num [cell12666])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12666

/-! Source-cell containment and simple scalar guards at 12666. -/
namespace BstLean.Part269.N12666
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12666)
open BstLean.Part268 (cell12666)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12666 ⟨10,by decide⟩).lower ∧ (cell12666 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12666 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12666 ⟨11,by decide⟩).lower ∧ (cell12666 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12666 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12666 ⟨12,by decide⟩).lower ∧ (cell12666 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12666 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12666 ⟨13,by decide⟩).lower ∧ (cell12666 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12666 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12666 ⟨14,by decide⟩).lower ∧ (cell12666 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12666 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12666 ⟨15,by decide⟩).lower ∧ (cell12666 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12666 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12666 ⟨16,by decide⟩).lower ∧ (cell12666 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12666 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12666 ⟨17,by decide⟩).lower ∧ (cell12666 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12666 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12666 ⟨18,by decide⟩).lower ∧ (cell12666 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12666 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12666 ⟨19,by decide⟩).lower ∧ (cell12666 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12666 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12666 ⟨20,by decide⟩).lower ∧ (cell12666 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12666 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12666 ⟨21,by decide⟩).lower ∧ (cell12666 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12666 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12666 ⟨22,by decide⟩).lower ∧ (cell12666 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12666 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12666 ⟨23,by decide⟩).lower ∧ (cell12666 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12666 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12666 ⟨24,by decide⟩).lower ∧ (cell12666 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12666 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12666 ⟨25,by decide⟩).lower ∧ (cell12666 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12666 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12666 ⟨26,by decide⟩).lower ∧ (cell12666 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12666 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12666 ⟨27,by decide⟩).lower ∧ (cell12666 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12666 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12666 ⟨28,by decide⟩).lower ∧ (cell12666 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12666 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12666 ⟨29,by decide⟩).lower ∧ (cell12666 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12666 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12666 ⟨30,by decide⟩).lower ∧ (cell12666 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12666 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12666 ⟨31,by decide⟩).lower ∧ (cell12666 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12666 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12666 ⟨32,by decide⟩).lower ∧ (cell12666 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12666 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12666 ⟨33,by decide⟩).lower ∧ (cell12666 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12666 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12666 ⟨34,by decide⟩).lower ∧ (cell12666 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12666 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12666 ⟨35,by decide⟩).lower ∧ (cell12666 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12666 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12666 ⟨36,by decide⟩).lower ∧ (cell12666 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12666 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12666 ⟨37,by decide⟩).lower ∧ (cell12666 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12666 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12666 ⟨38,by decide⟩).lower ∧ (cell12666 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12666 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12666 ⟨39,by decide⟩).lower ∧ (cell12666 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12666 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12666 ⟨40,by decide⟩).lower ∧ (cell12666 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12666 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12666 ⟨41,by decide⟩).lower ∧ (cell12666 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12666 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12666 ⟨42,by decide⟩).lower ∧ (cell12666 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12666 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12666 ⟨43,by decide⟩).lower ∧ (cell12666 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12666 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12666 ⟨44,by decide⟩).lower ∧ (cell12666 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12666 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12666 ⟨45,by decide⟩).lower ∧ (cell12666 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12666 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12666 ⟨46,by decide⟩).lower ∧ (cell12666 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12666 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12666 ⟨47,by decide⟩).lower ∧ (cell12666 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12666 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12666 ⟨48,by decide⟩).lower ∧ (cell12666 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12666 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12666 ⟨49,by decide⟩).lower ∧ (cell12666 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12666 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12666 ⟨50,by decide⟩).lower ∧ (cell12666 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12666 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12666 ⟨51,by decide⟩).lower ∧ (cell12666 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12666 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12666 ⟨52,by decide⟩).lower ∧ (cell12666 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12666 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12666 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12666 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12666,cell12666,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12666 i).lower ∧
    (cell12666 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12666 i).upper ≤ (0.532 : ℝ) ∧
    (cell12666 i).centre ≤ (0.1 : ℝ) ∧ (cell12666 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12666 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12666 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12666

/-! The local source numeric instances at 12666 have no network premises. -/
namespace BstLean.Part269.N12666
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12666)
open BstLean.Part268 (cell12666)

noncomputable def sourceNumerics12666 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12666 (cell12666 i)
      scalarRow12666.M scalarRow12666.H scalarRow12666.xi := by
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
    energy_allowance := scalarRow12666.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12666]
    centre_nonneg := (scalarRow12666.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12666])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12666
/-! Actual 12667 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12667
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12667 ≤ (1.035856246195 : ℝ) := by
  have hr : (112.547767636679 : ℝ) ≤ √(12667 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.547767636679 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12667 12667 (11 / 1000) ≤
    (0.008493167468 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12667) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.547767636679 : ℝ) ≤ √(12667 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12667)
  have hdiv : K / √(12667 : ℝ) ≤ K / 112.547767636679 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.547767636679 ≤ (0.008493167468 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12667.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12667 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12667 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12667 := gPlus_lower 12667
end BstLean.Part269.N12667

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12667
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035856246194 : ℝ) ≤ wn 12667 := by
  have hn : √(12667 : ℝ) ≤ 112.547767636680 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12667 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.547767636680 ≤ 2 / √(12667 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252548533 : ℝ) ≤ rhoBar 12667 BstLean.Part154.csC ∧
    rhoBar 12667 BstLean.Part154.csC ≤ 0.000252548924 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035856246194 : ℝ) / (1.295212 * 12667) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035856246195 : ℝ) / (1.29521 * 12667) := by gcongr
      _ ≤ (0.000252548924 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12667 BstLean.Part154.csC) ≤ 0.001010259477 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12667 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12667 BstLean.Part154.csC) (piBar (rhoBar 12667 BstLean.Part154.csC)) ≤ 0.000192898596 ∧
    cc1 (rhoBar 12667 BstLean.Part154.csC) (piBar (rhoBar 12667 BstLean.Part154.csC)) ≤ 0.000122742652 ∧
    cc2 (rhoBar 12667 BstLean.Part154.csC) ≤ 0.000071253044 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12667 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12667 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12667 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12667 BstLean.Part154.csC * nuR (rhoBar 12667 BstLean.Part154.csC)) ≤ 0.000505113793 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252548924 : ℝ) * 0.001010259477 := by gcongr
      _ ≤ (0.000505113793 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12667 BstLean.Part154.csC) * nuR (rhoBar 12667 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001010259477 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12667 BstLean.Part154.csC) * rhoBar 12667 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252548924 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252548924 / 2 + 0.399 * 0.001010259477 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192898596 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505113793 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122742652 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252548924 / 1.414213562 := by gcongr
      _ ≤ (0.000071253044 : ℝ) := by norm_num

end BstLean.Part269.N12667

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12667
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12667 BstLean.Part154.csC) (piBar (rhoBar 12667 BstLean.Part154.csC)) ≤ 1.60692E-7 := by
  have hr0 : 0 ≤ rhoBar 12667 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12667 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12667 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12667 BstLean.Part154.csC) (piBar (rhoBar 12667 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12667 BstLean.Part154.csC) (piBar (rhoBar 12667 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12667 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192898596 : ℝ) ^ 2 + 0.000122742652 ^ 2 + 3 * 0.000071253044 ^ 2 +
        2 * 0.797885 * 0.000192898596 * 0.000122742652 + 2 * 0.000192898596 * 0.000071253044 +
        4 * 0.797885 * 0.000122742652 * 0.000071253044 := by gcongr
    _ ≤ (1.60692E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12667 BstLean.Part154.csC Θ ≤ 0.002636385331 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12667 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12667 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12667 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12667 BstLean.Part154.csC) (piBar (rhoBar 12667 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12667 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035856246195 * 1.60692E-7 / (0.000252548533 : ℝ) := by gcongr
    _ ≤ 0.002636385331 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12667 BstLean.Part154.csC Θ ≤ 0.002925337129 + 0.000666170223 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12667 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12667 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12667 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035856246195 : ℝ) * ((2 * Θ * 0.000252548924 +
        (6863 / 10000) * 0.000252548924 * 12667 * 0.001010259477) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002925337129 + 0.000666170223 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12667 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12667 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12667 0.011 Θ ∧ gammaRatio 12667 0.011 Θ ≤ 0.000086819790 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12667 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035856246195 : ℝ) * 0.525 / ((1 - 0.011) * 12667) := by gcongr
      _ ≤ (0.000086819790 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12667 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12667 0.011 Θ) :=
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
    badAllowance 12667 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12667 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12667 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12667 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12667 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12667 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12667 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12667 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12667 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12667 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12667 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035856246195 : ℝ) * 12667 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12667 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003539648520 + 0.003302555554 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12667

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12667
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12667 BstLean.Part154.csC) (piBar (rhoBar 12667 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12667 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12667 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12667 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12667 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12667 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12667 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12667 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12667 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12667 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12667 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12667 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12667 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12667 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12667 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052553376061 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12667) ≤ 0.010610939748 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12667 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035856246195)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010610939748 + 2 * 0.737676 / 12667) := by gcongr
    _ ≤ (0.052553376061 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12667 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12667

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12667
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502072045 : ℝ) ≤ plow 12667 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12667) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052780090186)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384102299) : eMP 12667 0.011 xi bn ≤ 0.001191530754 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12667 : ℝ) * (1 - 0.011))) ≤ 0.000589147480 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001384102299 / (12667 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589147480 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589147480 : ℝ) + 3.141593 * 0.052780090186 / (12667 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001191530754 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052780090186)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384102299) : PiBarMP 12667 12 0.011 xi bn ≤ 0.161462938535 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12667 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037203525358 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.927043202257 : ℝ) ≤ √((12667 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.547767636679 : ℝ) ≤ √(12667 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12667) ≤ 0.123791067165 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037203525358 + 0.052780090186 * 1.772454 / (2 * (111.927043202257 : ℝ))) * (1 + 0.001191530754) +
        8 / (12667 * 112.547767636679) + 0.123791067165 := by gcongr
    _ ≤ (0.161462938535 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052780090186)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384102299) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282292554666) :
    parallelOracle 12667 0.011 xi bn cd ≤ 0.162455823794 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12667 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12667 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502072045 : ℝ) ≤ plow 12667 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.547767636679 : ℝ) ≤ √(12667 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282292554666 : ℝ) / (2 * 0.560502072045 * 112.547767636679)) * 0.161462938535 +
        0.282292554666 ^ 2 / (2 * 0.560502072045 * 112.547767636679) := by gcongr
    _ ≤ (0.162455823794 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052780090186) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001384102299)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282292554666) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12667 12667 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502072045 : ℝ) ≤ plow 12667 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.547767636679 : ℝ) ≤ √(12667 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12667 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12667 Θ 1.22 ≤ 0.011782557112 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.547767636679 := by gcongr <;> linarith
      _ ≤ (0.011782557112 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12667 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12667 12667 0.011 ≤ 0.008493167468 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12667 12667 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12667 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12667 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12667 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12667 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162455823794 + 0.011782557112 + (0.008493167468 : ℝ) *
        (1 + 2 * (0.282292554666 + 0.011782557112) / (0.560502072045 * 112.547767636679))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12667]

end BstLean.Part269.N12667

/-! The original eight local profiles supply actual 12667 moment certificates. -/
namespace BstLean.Part269.N12667
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12667 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12667 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12667 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052780090186 ∧
    0 ≤ bN 12667 BstLean.Part154.csC (groupTheta g) ∧ bN 12667 BstLean.Part154.csC (groupTheta g) ≤ 0.001384102299 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12667 12667 0.011
      (momentAllowance 12667 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12667 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12667 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12667 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12667 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12667 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229739178605 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12667 0.011
      (momentAllowance 12667 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12667 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12667
/-! The actual computed-centre upper energy formula at 12667. -/
namespace BstLean.Part269.N12667
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12667

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12667
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12667)
open BstLean.Part268 (cell12667)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085587090786
  | 2 => 0.086531632717
  | 3 => 0.087474577986
  | 4 => 0.088417405246
  | 5 => 0.089361900980
  | 6 => 0.090310204963
  | 7 => 0.091264859944
  | 8 => 0.092228865600
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12667 12667 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12667 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12667

/-! Actual upper energy certificates on all 43 source endpoints at 12667. -/
namespace BstLean.Part269.N12667
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12667)
open BstLean.Part268 (cell12667)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12667 (gMinus 12667) (1 - (cell12667 i).lower) ≤ 1 ∧
    energyUpper 12667 (gMinus 12667) (BstLean.Part211.gPlus 12667)
      (finiteEnergy 12667 12667 0.011) (1 - (cell12667 i).lower) ≤
      (cell12667 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨10,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨11,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨12,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨13,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨14,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨15,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨16,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨17,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨18,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨19,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨20,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨21,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨22,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨23,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨24,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨25,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨26,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨27,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨28,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨29,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨30,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨31,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨32,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨33,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨34,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨35,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨36,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨37,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨38,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨39,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨40,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨41,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨42,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨43,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨44,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨45,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨46,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨47,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨48,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨49,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨50,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨51,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12667) (by norm_num)
        (q := 1 - (cell12667 ⟨52,by decide⟩).lower)
        (by norm_num [cell12667]) (by norm_num [cell12667])
      exact ⟨E.1,E.2.trans (by norm_num [cell12667])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12667

/-! Source-cell containment and simple scalar guards at 12667. -/
namespace BstLean.Part269.N12667
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12667)
open BstLean.Part268 (cell12667)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12667 ⟨10,by decide⟩).lower ∧ (cell12667 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12667 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12667 ⟨11,by decide⟩).lower ∧ (cell12667 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12667 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12667 ⟨12,by decide⟩).lower ∧ (cell12667 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12667 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12667 ⟨13,by decide⟩).lower ∧ (cell12667 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12667 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12667 ⟨14,by decide⟩).lower ∧ (cell12667 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12667 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12667 ⟨15,by decide⟩).lower ∧ (cell12667 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12667 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12667 ⟨16,by decide⟩).lower ∧ (cell12667 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12667 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12667 ⟨17,by decide⟩).lower ∧ (cell12667 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12667 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12667 ⟨18,by decide⟩).lower ∧ (cell12667 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12667 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12667 ⟨19,by decide⟩).lower ∧ (cell12667 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12667 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12667 ⟨20,by decide⟩).lower ∧ (cell12667 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12667 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12667 ⟨21,by decide⟩).lower ∧ (cell12667 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12667 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12667 ⟨22,by decide⟩).lower ∧ (cell12667 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12667 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12667 ⟨23,by decide⟩).lower ∧ (cell12667 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12667 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12667 ⟨24,by decide⟩).lower ∧ (cell12667 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12667 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12667 ⟨25,by decide⟩).lower ∧ (cell12667 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12667 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12667 ⟨26,by decide⟩).lower ∧ (cell12667 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12667 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12667 ⟨27,by decide⟩).lower ∧ (cell12667 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12667 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12667 ⟨28,by decide⟩).lower ∧ (cell12667 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12667 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12667 ⟨29,by decide⟩).lower ∧ (cell12667 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12667 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12667 ⟨30,by decide⟩).lower ∧ (cell12667 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12667 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12667 ⟨31,by decide⟩).lower ∧ (cell12667 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12667 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12667 ⟨32,by decide⟩).lower ∧ (cell12667 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12667 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12667 ⟨33,by decide⟩).lower ∧ (cell12667 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12667 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12667 ⟨34,by decide⟩).lower ∧ (cell12667 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12667 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12667 ⟨35,by decide⟩).lower ∧ (cell12667 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12667 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12667 ⟨36,by decide⟩).lower ∧ (cell12667 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12667 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12667 ⟨37,by decide⟩).lower ∧ (cell12667 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12667 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12667 ⟨38,by decide⟩).lower ∧ (cell12667 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12667 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12667 ⟨39,by decide⟩).lower ∧ (cell12667 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12667 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12667 ⟨40,by decide⟩).lower ∧ (cell12667 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12667 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12667 ⟨41,by decide⟩).lower ∧ (cell12667 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12667 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12667 ⟨42,by decide⟩).lower ∧ (cell12667 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12667 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12667 ⟨43,by decide⟩).lower ∧ (cell12667 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12667 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12667 ⟨44,by decide⟩).lower ∧ (cell12667 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12667 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12667 ⟨45,by decide⟩).lower ∧ (cell12667 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12667 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12667 ⟨46,by decide⟩).lower ∧ (cell12667 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12667 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12667 ⟨47,by decide⟩).lower ∧ (cell12667 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12667 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12667 ⟨48,by decide⟩).lower ∧ (cell12667 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12667 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12667 ⟨49,by decide⟩).lower ∧ (cell12667 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12667 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12667 ⟨50,by decide⟩).lower ∧ (cell12667 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12667 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12667 ⟨51,by decide⟩).lower ∧ (cell12667 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12667 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12667 ⟨52,by decide⟩).lower ∧ (cell12667 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12667 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12667 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12667 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12667,cell12667,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12667 i).lower ∧
    (cell12667 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12667 i).upper ≤ (0.532 : ℝ) ∧
    (cell12667 i).centre ≤ (0.1 : ℝ) ∧ (cell12667 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12667 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12667 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12667

/-! The local source numeric instances at 12667 have no network premises. -/
namespace BstLean.Part269.N12667
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12667)
open BstLean.Part268 (cell12667)

noncomputable def sourceNumerics12667 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12667 (cell12667 i)
      scalarRow12667.M scalarRow12667.H scalarRow12667.xi := by
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
    energy_allowance := scalarRow12667.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12667]
    centre_nonneg := (scalarRow12667.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12667])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12667
/-! Actual 12668 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12668
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12668 ≤ (1.035854818474 : ℝ) := by
  have hr : (112.552210107132 : ℝ) ≤ √(12668 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.552210107132 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12668 12668 (11 / 1000) ≤
    (0.008492832238 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12668) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.552210107132 : ℝ) ≤ √(12668 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12668)
  have hdiv : K / √(12668 : ℝ) ≤ K / 112.552210107132 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.552210107132 ≤ (0.008492832238 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12668.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12668 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12668 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12668 := gPlus_lower 12668
end BstLean.Part269.N12668

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12668
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035854818473 : ℝ) ≤ wn 12668 := by
  have hn : √(12668 : ℝ) ≤ 112.552210107133 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12668 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.552210107133 ≤ 2 / √(12668 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252528249 : ℝ) ≤ rhoBar 12668 BstLean.Part154.csC ∧
    rhoBar 12668 BstLean.Part154.csC ≤ 0.000252528640 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035854818473 : ℝ) / (1.295212 * 12668) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035854818474 : ℝ) / (1.29521 * 12668) := by gcongr
      _ ≤ (0.000252528640 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12668 BstLean.Part154.csC) ≤ 0.001010178331 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12668 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12668 BstLean.Part154.csC) (piBar (rhoBar 12668 BstLean.Part154.csC)) ≤ 0.000192883102 ∧
    cc1 (rhoBar 12668 BstLean.Part154.csC) (piBar (rhoBar 12668 BstLean.Part154.csC)) ≤ 0.000122732794 ∧
    cc2 (rhoBar 12668 BstLean.Part154.csC) ≤ 0.000071247321 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12668 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12668 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12668 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12668 BstLean.Part154.csC * nuR (rhoBar 12668 BstLean.Part154.csC)) ≤ 0.000505073223 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252528640 : ℝ) * 0.001010178331 := by gcongr
      _ ≤ (0.000505073223 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12668 BstLean.Part154.csC) * nuR (rhoBar 12668 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001010178331 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12668 BstLean.Part154.csC) * rhoBar 12668 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252528640 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252528640 / 2 + 0.399 * 0.001010178331 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192883102 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505073223 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122732794 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252528640 / 1.414213562 := by gcongr
      _ ≤ (0.000071247321 : ℝ) := by norm_num

end BstLean.Part269.N12668

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12668
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12668 BstLean.Part154.csC) (piBar (rhoBar 12668 BstLean.Part154.csC)) ≤ 1.60666E-7 := by
  have hr0 : 0 ≤ rhoBar 12668 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12668 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12668 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12668 BstLean.Part154.csC) (piBar (rhoBar 12668 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12668 BstLean.Part154.csC) (piBar (rhoBar 12668 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12668 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192883102 : ℝ) ^ 2 + 0.000122732794 ^ 2 + 3 * 0.000071247321 ^ 2 +
        2 * 0.797885 * 0.000192883102 * 0.000122732794 + 2 * 0.000192883102 * 0.000071247321 +
        4 * 0.797885 * 0.000122732794 * 0.000071247321 := by gcongr
    _ ≤ (1.60666E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12668 BstLean.Part154.csC Θ ≤ 0.002636166860 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12668 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12668 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12668 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12668 BstLean.Part154.csC) (piBar (rhoBar 12668 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12668 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035854818474 * 1.60666E-7 / (0.000252528249 : ℝ) := by gcongr
    _ ≤ 0.002636166860 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12668 BstLean.Part154.csC Θ ≤ 0.002925094097 + 0.000666115801 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12668 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12668 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12668 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035854818474 : ℝ) * ((2 * Θ * 0.000252528640 +
        (6863 / 10000) * 0.000252528640 * 12668 * 0.001010178331) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002925094097 + 0.000666115801 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12668 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12668 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12668 0.011 Θ ∧ gammaRatio 12668 0.011 Θ ≤ 0.000086812816 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12668 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035854818474 : ℝ) * 0.525 / ((1 - 0.011) * 12668) := by gcongr
      _ ≤ (0.000086812816 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12668 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12668 0.011 Θ) :=
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
    badAllowance 12668 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12668 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12668 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12668 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12668 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12668 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12668 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12668 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12668 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12668 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12668 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035854818474 : ℝ) * 12668 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12668 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003539405488 + 0.003302282661 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12668

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12668
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12668 BstLean.Part154.csC) (piBar (rhoBar 12668 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12668 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12668 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12668 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12668 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12668 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12668 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12668 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12668 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12668 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12668 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12668 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12668 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12668 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12668 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052551279237 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12668) ≤ 0.010610520930 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12668 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035854818474)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010610520930 + 2 * 0.737676 / 12668) := by gcongr
    _ ≤ (0.052551279237 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12668 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12668

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12668
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502117500 : ℝ) ≤ plow 12668 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12668) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052779703886)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383987602) : eMP 12668 0.011 xi bn ≤ 0.001191434284 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12668 : ℝ) * (1 - 0.011))) ≤ 0.000589099816 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001383987602 / (12668 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589099816 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589099816 : ℝ) + 3.141593 * 0.052779703886 / (12668 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001191434284 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052779703886)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383987602) : PiBarMP 12668 12 0.011 xi bn ≤ 0.161456485243 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12668 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037201983845 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.931461171558 : ℝ) ≤ √((12668 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.552210107132 : ℝ) ≤ √(12668 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12668) ≤ 0.123786181094 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037201983845 + 0.052779703886 * 1.772454 / (2 * (111.931461171558 : ℝ))) * (1 + 0.001191434284) +
        8 / (12668 * 112.552210107132) + 0.123786181094 := by gcongr
    _ ≤ (0.161456485243 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052779703886)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383987602) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282289617105) :
    parallelOracle 12668 0.011 xi bn cd ≤ 0.162449299890 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12668 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12668 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502117500 : ℝ) ≤ plow 12668 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.552210107132 : ℝ) ≤ √(12668 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282289617105 : ℝ) / (2 * 0.560502117500 * 112.552210107132)) * 0.161456485243 +
        0.282289617105 ^ 2 / (2 * 0.560502117500 * 112.552210107132) := by gcongr
    _ ≤ (0.162449299890 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052779703886) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383987602)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282289617105) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12668 12668 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502117500 : ℝ) ≤ plow 12668 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.552210107132 : ℝ) ≤ √(12668 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12668 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12668 Θ 1.22 ≤ 0.011782092051 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.552210107132 := by gcongr <;> linarith
      _ ≤ (0.011782092051 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12668 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12668 12668 0.011 ≤ 0.008492832238 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12668 12668 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12668 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12668 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12668 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12668 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162449299890 + 0.011782092051 + (0.008492832238 : ℝ) *
        (1 + 2 * (0.282289617105 + 0.011782092051) / (0.560502117500 * 112.552210107132))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12668]

end BstLean.Part269.N12668

/-! The original eight local profiles supply actual 12668 moment certificates. -/
namespace BstLean.Part269.N12668
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12668 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12668 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12668 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052779703886 ∧
    0 ≤ bN 12668 BstLean.Part154.csC (groupTheta g) ∧ bN 12668 BstLean.Part154.csC (groupTheta g) ≤ 0.001383987602 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12668 12668 0.011
      (momentAllowance 12668 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12668 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12668 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12668 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12668 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12668 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229738337868 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12668 0.011
      (momentAllowance 12668 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12668 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12668
/-! The actual computed-centre upper energy formula at 12668. -/
namespace BstLean.Part269.N12668
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12668

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12668
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12668)
open BstLean.Part268 (cell12668)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085584138675
  | 2 => 0.086528625551
  | 3 => 0.087471507601
  | 4 => 0.088414261608
  | 5 => 0.089358671856
  | 6 => 0.090306875549
  | 7 => 0.091261412458
  | 8 => 0.092225278820
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12668 12668 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12668 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12668

/-! Actual upper energy certificates on all 43 source endpoints at 12668. -/
namespace BstLean.Part269.N12668
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12668)
open BstLean.Part268 (cell12668)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12668 (gMinus 12668) (1 - (cell12668 i).lower) ≤ 1 ∧
    energyUpper 12668 (gMinus 12668) (BstLean.Part211.gPlus 12668)
      (finiteEnergy 12668 12668 0.011) (1 - (cell12668 i).lower) ≤
      (cell12668 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨10,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨11,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨12,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨13,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨14,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨15,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨16,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨17,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨18,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨19,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨20,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨21,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨22,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨23,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨24,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨25,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨26,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨27,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨28,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨29,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨30,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨31,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨32,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨33,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨34,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨35,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨36,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨37,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨38,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨39,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨40,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨41,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨42,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨43,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨44,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨45,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨46,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨47,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨48,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨49,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨50,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨51,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12668) (by norm_num)
        (q := 1 - (cell12668 ⟨52,by decide⟩).lower)
        (by norm_num [cell12668]) (by norm_num [cell12668])
      exact ⟨E.1,E.2.trans (by norm_num [cell12668])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12668

/-! Source-cell containment and simple scalar guards at 12668. -/
namespace BstLean.Part269.N12668
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12668)
open BstLean.Part268 (cell12668)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12668 ⟨10,by decide⟩).lower ∧ (cell12668 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12668 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12668 ⟨11,by decide⟩).lower ∧ (cell12668 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12668 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12668 ⟨12,by decide⟩).lower ∧ (cell12668 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12668 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12668 ⟨13,by decide⟩).lower ∧ (cell12668 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12668 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12668 ⟨14,by decide⟩).lower ∧ (cell12668 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12668 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12668 ⟨15,by decide⟩).lower ∧ (cell12668 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12668 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12668 ⟨16,by decide⟩).lower ∧ (cell12668 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12668 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12668 ⟨17,by decide⟩).lower ∧ (cell12668 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12668 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12668 ⟨18,by decide⟩).lower ∧ (cell12668 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12668 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12668 ⟨19,by decide⟩).lower ∧ (cell12668 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12668 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12668 ⟨20,by decide⟩).lower ∧ (cell12668 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12668 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12668 ⟨21,by decide⟩).lower ∧ (cell12668 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12668 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12668 ⟨22,by decide⟩).lower ∧ (cell12668 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12668 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12668 ⟨23,by decide⟩).lower ∧ (cell12668 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12668 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12668 ⟨24,by decide⟩).lower ∧ (cell12668 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12668 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12668 ⟨25,by decide⟩).lower ∧ (cell12668 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12668 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12668 ⟨26,by decide⟩).lower ∧ (cell12668 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12668 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12668 ⟨27,by decide⟩).lower ∧ (cell12668 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12668 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12668 ⟨28,by decide⟩).lower ∧ (cell12668 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12668 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12668 ⟨29,by decide⟩).lower ∧ (cell12668 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12668 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12668 ⟨30,by decide⟩).lower ∧ (cell12668 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12668 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12668 ⟨31,by decide⟩).lower ∧ (cell12668 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12668 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12668 ⟨32,by decide⟩).lower ∧ (cell12668 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12668 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12668 ⟨33,by decide⟩).lower ∧ (cell12668 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12668 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12668 ⟨34,by decide⟩).lower ∧ (cell12668 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12668 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12668 ⟨35,by decide⟩).lower ∧ (cell12668 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12668 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12668 ⟨36,by decide⟩).lower ∧ (cell12668 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12668 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12668 ⟨37,by decide⟩).lower ∧ (cell12668 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12668 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12668 ⟨38,by decide⟩).lower ∧ (cell12668 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12668 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12668 ⟨39,by decide⟩).lower ∧ (cell12668 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12668 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12668 ⟨40,by decide⟩).lower ∧ (cell12668 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12668 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12668 ⟨41,by decide⟩).lower ∧ (cell12668 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12668 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12668 ⟨42,by decide⟩).lower ∧ (cell12668 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12668 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12668 ⟨43,by decide⟩).lower ∧ (cell12668 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12668 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12668 ⟨44,by decide⟩).lower ∧ (cell12668 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12668 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12668 ⟨45,by decide⟩).lower ∧ (cell12668 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12668 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12668 ⟨46,by decide⟩).lower ∧ (cell12668 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12668 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12668 ⟨47,by decide⟩).lower ∧ (cell12668 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12668 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12668 ⟨48,by decide⟩).lower ∧ (cell12668 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12668 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12668 ⟨49,by decide⟩).lower ∧ (cell12668 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12668 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12668 ⟨50,by decide⟩).lower ∧ (cell12668 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12668 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12668 ⟨51,by decide⟩).lower ∧ (cell12668 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12668 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12668 ⟨52,by decide⟩).lower ∧ (cell12668 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12668 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12668 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12668 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12668,cell12668,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12668 i).lower ∧
    (cell12668 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12668 i).upper ≤ (0.532 : ℝ) ∧
    (cell12668 i).centre ≤ (0.1 : ℝ) ∧ (cell12668 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12668 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12668 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12668

/-! The local source numeric instances at 12668 have no network premises. -/
namespace BstLean.Part269.N12668
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12668)
open BstLean.Part268 (cell12668)

noncomputable def sourceNumerics12668 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12668 (cell12668 i)
      scalarRow12668.M scalarRow12668.H scalarRow12668.xi := by
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
    energy_allowance := scalarRow12668.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12668]
    centre_nonneg := (scalarRow12668.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12668])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12668
/-! Actual 12669 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12669
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12669 ≤ (1.035853390924 : ℝ) := by
  have hr : (112.556652402245 : ℝ) ≤ √(12669 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.556652402245 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12669 12669 (11 / 1000) ≤
    (0.008492497047 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12669) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.556652402245 : ℝ) ≤ √(12669 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12669)
  have hdiv : K / √(12669 : ℝ) ≤ K / 112.556652402245 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.556652402245 ≤ (0.008492497047 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12669.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12669 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12669 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12669 := gPlus_lower 12669
end BstLean.Part269.N12669

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12669
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035853390923 : ℝ) ≤ wn 12669 := by
  have hn : √(12669 : ℝ) ≤ 112.556652402246 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12669 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.556652402246 ≤ 2 / √(12669 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252507968 : ℝ) ≤ rhoBar 12669 BstLean.Part154.csC ∧
    rhoBar 12669 BstLean.Part154.csC ≤ 0.000252508359 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035853390923 : ℝ) / (1.295212 * 12669) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035853390924 : ℝ) / (1.29521 * 12669) := by gcongr
      _ ≤ (0.000252508359 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12669 BstLean.Part154.csC) ≤ 0.001010097197 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12669 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12669 BstLean.Part154.csC) (piBar (rhoBar 12669 BstLean.Part154.csC)) ≤ 0.000192867610 ∧
    cc1 (rhoBar 12669 BstLean.Part154.csC) (piBar (rhoBar 12669 BstLean.Part154.csC)) ≤ 0.000122722936 ∧
    cc2 (rhoBar 12669 BstLean.Part154.csC) ≤ 0.000071241599 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12669 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12669 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12669 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12669 BstLean.Part154.csC * nuR (rhoBar 12669 BstLean.Part154.csC)) ≤ 0.000505032658 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252508359 : ℝ) * 0.001010097197 := by gcongr
      _ ≤ (0.000505032658 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12669 BstLean.Part154.csC) * nuR (rhoBar 12669 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001010097197 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12669 BstLean.Part154.csC) * rhoBar 12669 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252508359 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252508359 / 2 + 0.399 * 0.001010097197 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192867610 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000505032658 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122722936 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252508359 / 1.414213562 := by gcongr
      _ ≤ (0.000071241599 : ℝ) := by norm_num

end BstLean.Part269.N12669

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12669
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12669 BstLean.Part154.csC) (piBar (rhoBar 12669 BstLean.Part154.csC)) ≤ 1.60640E-7 := by
  have hr0 : 0 ≤ rhoBar 12669 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12669 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12669 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12669 BstLean.Part154.csC) (piBar (rhoBar 12669 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12669 BstLean.Part154.csC) (piBar (rhoBar 12669 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12669 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192867610 : ℝ) ^ 2 + 0.000122722936 ^ 2 + 3 * 0.000071241599 ^ 2 +
        2 * 0.797885 * 0.000192867610 * 0.000122722936 + 2 * 0.000192867610 * 0.000071241599 +
        4 * 0.797885 * 0.000122722936 * 0.000071241599 := by gcongr
    _ ≤ (1.60640E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12669 BstLean.Part154.csC Θ ≤ 0.002635948324 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12669 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12669 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12669 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12669 BstLean.Part154.csC) (piBar (rhoBar 12669 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12669 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035853390924 * 1.60640E-7 / (0.000252507968 : ℝ) := by gcongr
    _ ≤ 0.002635948324 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12669 BstLean.Part154.csC Θ ≤ 0.002924851100 + 0.000666061386 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12669 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12669 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12669 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035853390924 : ℝ) * ((2 * Θ * 0.000252508359 +
        (6863 / 10000) * 0.000252508359 * 12669 * 0.001010097197) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002924851100 + 0.000666061386 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12669 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12669 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12669 0.011 Θ ∧ gammaRatio 12669 0.011 Θ ≤ 0.000086805844 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12669 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035853390924 : ℝ) * 0.525 / ((1 - 0.011) * 12669) := by gcongr
      _ ≤ (0.000086805844 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12669 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12669 0.011 Θ) :=
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
    badAllowance 12669 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12669 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12669 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12669 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12669 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12669 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12669 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12669 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12669 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12669 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12669 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035853390924 : ℝ) * 12669 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12669 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003539162491 + 0.003302009710 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12669

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12669
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12669 BstLean.Part154.csC) (piBar (rhoBar 12669 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12669 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12669 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12669 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12669 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12669 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12669 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12669 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12669 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12669 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12669 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12669 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12669 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12669 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12669 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052549182671 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12669) ≤ 0.010610102163 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12669 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035853390924)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010610102163 + 2 * 0.737676 / 12669) := by gcongr
    _ ≤ (0.052549182671 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12669 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12669

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12669
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502162948 : ℝ) ≤ plow 12669 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12669) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052779317589)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383872871) : eMP 12669 0.011 xi bn ≤ 0.001191337809 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12669 : ℝ) * (1 - 0.011))) ≤ 0.000589052149 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001383872871 / (12669 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589052149 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589052149 : ℝ) + 3.141593 * 0.052779317589 / (12669 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001191337809 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052779317589)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383872871) : PiBarMP 12669 12 0.011 xi bn ≤ 0.161450032012 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12669 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037200441812 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.935878966486 : ℝ) ≤ √((12669 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.556652402245 : ℝ) ≤ √(12669 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12669) ≤ 0.123781295601 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037200441812 + 0.052779317589 * 1.772454 / (2 * (111.935878966486 : ℝ))) * (1 + 0.001191337809) +
        8 / (12669 * 112.556652402245) + 0.123781295601 := by gcongr
    _ ≤ (0.161450032012 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052779317589)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383872871) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282286679805) :
    parallelOracle 12669 0.011 xi bn cd ≤ 0.162442776056 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12669 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12669 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502162948 : ℝ) ≤ plow 12669 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.556652402245 : ℝ) ≤ √(12669 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282286679805 : ℝ) / (2 * 0.560502162948 * 112.556652402245)) * 0.161450032012 +
        0.282286679805 ^ 2 / (2 * 0.560502162948 * 112.556652402245) := by gcongr
    _ ≤ (0.162442776056 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052779317589) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383872871)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282286679805) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12669 12669 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502162948 : ℝ) ≤ plow 12669 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.556652402245 : ℝ) ≤ √(12669 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12669 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12669 Θ 1.22 ≤ 0.011781627045 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.556652402245 := by gcongr <;> linarith
      _ ≤ (0.011781627045 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12669 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12669 12669 0.011 ≤ 0.008492497047 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12669 12669 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12669 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12669 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12669 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12669 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162442776056 + 0.011781627045 + (0.008492497047 : ℝ) *
        (1 + 2 * (0.282286679805 + 0.011781627045) / (0.560502162948 * 112.556652402245))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12669]

end BstLean.Part269.N12669

/-! The original eight local profiles supply actual 12669 moment certificates. -/
namespace BstLean.Part269.N12669
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12669 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12669 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12669 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052779317589 ∧
    0 ≤ bN 12669 BstLean.Part154.csC (groupTheta g) ∧ bN 12669 BstLean.Part154.csC (groupTheta g) ≤ 0.001383872871 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12669 12669 0.011
      (momentAllowance 12669 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12669 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12669 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12669 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12669 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12669 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229737497134 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12669 0.011
      (momentAllowance 12669 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12669 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12669
/-! The actual computed-centre upper energy formula at 12669. -/
namespace BstLean.Part269.N12669
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12669

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12669
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12669)
open BstLean.Part268 (cell12669)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085581187684
  | 2 => 0.086525619551
  | 3 => 0.087468438440
  | 4 => 0.088411119264
  | 5 => 0.089355444112
  | 6 => 0.090303547620
  | 7 => 0.091257966583
  | 8 => 0.092221693803
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12669 12669 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12669 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12669

/-! Actual upper energy certificates on all 43 source endpoints at 12669. -/
namespace BstLean.Part269.N12669
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12669)
open BstLean.Part268 (cell12669)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12669 (gMinus 12669) (1 - (cell12669 i).lower) ≤ 1 ∧
    energyUpper 12669 (gMinus 12669) (BstLean.Part211.gPlus 12669)
      (finiteEnergy 12669 12669 0.011) (1 - (cell12669 i).lower) ≤
      (cell12669 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨10,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨11,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨12,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨13,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨14,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨15,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨16,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨17,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨18,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨19,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨20,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨21,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨22,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨23,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨24,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨25,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨26,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨27,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨28,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨29,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨30,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨31,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨32,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨33,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨34,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨35,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨36,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨37,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨38,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨39,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨40,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨41,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨42,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨43,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨44,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨45,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨46,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨47,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨48,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨49,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨50,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨51,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12669) (by norm_num)
        (q := 1 - (cell12669 ⟨52,by decide⟩).lower)
        (by norm_num [cell12669]) (by norm_num [cell12669])
      exact ⟨E.1,E.2.trans (by norm_num [cell12669])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12669

/-! Source-cell containment and simple scalar guards at 12669. -/
namespace BstLean.Part269.N12669
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12669)
open BstLean.Part268 (cell12669)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12669 ⟨10,by decide⟩).lower ∧ (cell12669 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12669 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12669 ⟨11,by decide⟩).lower ∧ (cell12669 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12669 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12669 ⟨12,by decide⟩).lower ∧ (cell12669 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12669 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12669 ⟨13,by decide⟩).lower ∧ (cell12669 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12669 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12669 ⟨14,by decide⟩).lower ∧ (cell12669 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12669 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12669 ⟨15,by decide⟩).lower ∧ (cell12669 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12669 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12669 ⟨16,by decide⟩).lower ∧ (cell12669 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12669 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12669 ⟨17,by decide⟩).lower ∧ (cell12669 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12669 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12669 ⟨18,by decide⟩).lower ∧ (cell12669 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12669 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12669 ⟨19,by decide⟩).lower ∧ (cell12669 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12669 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12669 ⟨20,by decide⟩).lower ∧ (cell12669 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12669 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12669 ⟨21,by decide⟩).lower ∧ (cell12669 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12669 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12669 ⟨22,by decide⟩).lower ∧ (cell12669 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12669 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12669 ⟨23,by decide⟩).lower ∧ (cell12669 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12669 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12669 ⟨24,by decide⟩).lower ∧ (cell12669 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12669 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12669 ⟨25,by decide⟩).lower ∧ (cell12669 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12669 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12669 ⟨26,by decide⟩).lower ∧ (cell12669 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12669 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12669 ⟨27,by decide⟩).lower ∧ (cell12669 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12669 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12669 ⟨28,by decide⟩).lower ∧ (cell12669 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12669 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12669 ⟨29,by decide⟩).lower ∧ (cell12669 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12669 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12669 ⟨30,by decide⟩).lower ∧ (cell12669 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12669 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12669 ⟨31,by decide⟩).lower ∧ (cell12669 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12669 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12669 ⟨32,by decide⟩).lower ∧ (cell12669 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12669 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12669 ⟨33,by decide⟩).lower ∧ (cell12669 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12669 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12669 ⟨34,by decide⟩).lower ∧ (cell12669 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12669 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12669 ⟨35,by decide⟩).lower ∧ (cell12669 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12669 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12669 ⟨36,by decide⟩).lower ∧ (cell12669 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12669 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12669 ⟨37,by decide⟩).lower ∧ (cell12669 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12669 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12669 ⟨38,by decide⟩).lower ∧ (cell12669 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12669 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12669 ⟨39,by decide⟩).lower ∧ (cell12669 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12669 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12669 ⟨40,by decide⟩).lower ∧ (cell12669 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12669 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12669 ⟨41,by decide⟩).lower ∧ (cell12669 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12669 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12669 ⟨42,by decide⟩).lower ∧ (cell12669 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12669 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12669 ⟨43,by decide⟩).lower ∧ (cell12669 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12669 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12669 ⟨44,by decide⟩).lower ∧ (cell12669 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12669 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12669 ⟨45,by decide⟩).lower ∧ (cell12669 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12669 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12669 ⟨46,by decide⟩).lower ∧ (cell12669 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12669 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12669 ⟨47,by decide⟩).lower ∧ (cell12669 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12669 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12669 ⟨48,by decide⟩).lower ∧ (cell12669 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12669 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12669 ⟨49,by decide⟩).lower ∧ (cell12669 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12669 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12669 ⟨50,by decide⟩).lower ∧ (cell12669 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12669 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12669 ⟨51,by decide⟩).lower ∧ (cell12669 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12669 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12669 ⟨52,by decide⟩).lower ∧ (cell12669 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12669 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12669 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12669 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12669,cell12669,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12669 i).lower ∧
    (cell12669 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12669 i).upper ≤ (0.532 : ℝ) ∧
    (cell12669 i).centre ≤ (0.1 : ℝ) ∧ (cell12669 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12669 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12669 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12669

/-! The local source numeric instances at 12669 have no network premises. -/
namespace BstLean.Part269.N12669
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12669)
open BstLean.Part268 (cell12669)

noncomputable def sourceNumerics12669 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12669 (cell12669 i)
      scalarRow12669.M scalarRow12669.H scalarRow12669.xi := by
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
    energy_allowance := scalarRow12669.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12669]
    centre_nonneg := (scalarRow12669.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12669])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12669
/-! Actual 12670 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12670
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12670 ≤ (1.035851963543 : ℝ) := by
  have hr : (112.561094522041 : ℝ) ≤ √(12670 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.561094522041 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12670 12670 (11 / 1000) ≤
    (0.008492161896 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12670) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.561094522041 : ℝ) ≤ √(12670 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12670)
  have hdiv : K / √(12670 : ℝ) ≤ K / 112.561094522041 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.561094522041 ≤ (0.008492161896 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12670.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12670 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12670 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12670 := gPlus_lower 12670
end BstLean.Part269.N12670

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12670
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035851963542 : ℝ) ≤ wn 12670 := by
  have hn : √(12670 : ℝ) ≤ 112.561094522042 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12670 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.561094522042 ≤ 2 / √(12670 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252487690 : ℝ) ≤ rhoBar 12670 BstLean.Part154.csC ∧
    rhoBar 12670 BstLean.Part154.csC ≤ 0.000252488081 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035851963542 : ℝ) / (1.295212 * 12670) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035851963543 : ℝ) / (1.29521 * 12670) := by gcongr
      _ ≤ (0.000252488081 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12670 BstLean.Part154.csC) ≤ 0.001010016075 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12670 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12670 BstLean.Part154.csC) (piBar (rhoBar 12670 BstLean.Part154.csC)) ≤ 0.000192852121 ∧
    cc1 (rhoBar 12670 BstLean.Part154.csC) (piBar (rhoBar 12670 BstLean.Part154.csC)) ≤ 0.000122713081 ∧
    cc2 (rhoBar 12670 BstLean.Part154.csC) ≤ 0.000071235878 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12670 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12670 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12670 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12670 BstLean.Part154.csC * nuR (rhoBar 12670 BstLean.Part154.csC)) ≤ 0.000504992100 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252488081 : ℝ) * 0.001010016075 := by gcongr
      _ ≤ (0.000504992100 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12670 BstLean.Part154.csC) * nuR (rhoBar 12670 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001010016075 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12670 BstLean.Part154.csC) * rhoBar 12670 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252488081 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252488081 / 2 + 0.399 * 0.001010016075 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192852121 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504992100 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122713081 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252488081 / 1.414213562 := by gcongr
      _ ≤ (0.000071235878 : ℝ) := by norm_num

end BstLean.Part269.N12670

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12670
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12670 BstLean.Part154.csC) (piBar (rhoBar 12670 BstLean.Part154.csC)) ≤ 1.60614E-7 := by
  have hr0 : 0 ≤ rhoBar 12670 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12670 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12670 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12670 BstLean.Part154.csC) (piBar (rhoBar 12670 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12670 BstLean.Part154.csC) (piBar (rhoBar 12670 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12670 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192852121 : ℝ) ^ 2 + 0.000122713081 ^ 2 + 3 * 0.000071235878 ^ 2 +
        2 * 0.797885 * 0.000192852121 * 0.000122713081 + 2 * 0.000192852121 * 0.000071235878 +
        4 * 0.797885 * 0.000122713081 * 0.000071235878 := by gcongr
    _ ≤ (1.60614E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12670 BstLean.Part154.csC Θ ≤ 0.002635729723 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12670 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12670 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12670 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12670 BstLean.Part154.csC) (piBar (rhoBar 12670 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12670 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035851963543 * 1.60614E-7 / (0.000252487690 : ℝ) := by gcongr
    _ ≤ 0.002635729723 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12670 BstLean.Part154.csC Θ ≤ 0.002924608136 + 0.000666006979 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12670 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12670 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12670 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035851963543 : ℝ) * ((2 * Θ * 0.000252488081 +
        (6863 / 10000) * 0.000252488081 * 12670 * 0.001010016075) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002924608136 + 0.000666006979 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12670 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12670 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12670 0.011 Θ ∧ gammaRatio 12670 0.011 Θ ≤ 0.000086798873 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12670 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035851963543 : ℝ) * 0.525 / ((1 - 0.011) * 12670) := by gcongr
      _ ≤ (0.000086798873 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12670 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12670 0.011 Θ) :=
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
    badAllowance 12670 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12670 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12670 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12670 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12670 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12670 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12670 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12670 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12670 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12670 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12670 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035851963543 : ℝ) * 12670 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12670 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003538919527 + 0.003301736702 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12670

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12670
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12670 BstLean.Part154.csC) (piBar (rhoBar 12670 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12670 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12670 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12670 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12670 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12670 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12670 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12670 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12670 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12670 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12670 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12670 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12670 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12670 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12670 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052547086352 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12670) ≤ 0.010609683445 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12670 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035851963543)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010609683445 + 2 * 0.737676 / 12670) := by gcongr
    _ ≤ (0.052547086352 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12670 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12670

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12670
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502208389 : ℝ) ≤ plow 12670 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12670) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052778931296)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383758105) : eMP 12670 0.011 xi bn ≤ 0.001191241326 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12670 : ℝ) * (1 - 0.011))) ≤ 0.000589004478 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001383758105 / (12670 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000589004478 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000589004478 : ℝ) + 3.141593 * 0.052778931296 / (12670 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001191241326 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052778931296)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383758105) : PiBarMP 12670 12 0.011 xi bn ≤ 0.161443578826 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12670 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037198899245 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.940296587064 : ℝ) ≤ √((12670 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.561094522041 : ℝ) ≤ √(12670 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12670) ≤ 0.123776410686 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037198899245 + 0.052778931296 * 1.772454 / (2 * (111.940296587064 : ℝ))) * (1 + 0.001191241326) +
        8 / (12670 * 112.561094522041) + 0.123776410686 := by gcongr
    _ ≤ (0.161443578826 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052778931296)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383758105) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282283742757) :
    parallelOracle 12670 0.011 xi bn cd ≤ 0.162436252276 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12670 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12670 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502208389 : ℝ) ≤ plow 12670 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.561094522041 : ℝ) ≤ √(12670 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282283742757 : ℝ) / (2 * 0.560502208389 * 112.561094522041)) * 0.161443578826 +
        0.282283742757 ^ 2 / (2 * 0.560502208389 * 112.561094522041) := by gcongr
    _ ≤ (0.162436252276 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052778931296) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383758105)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282283742757) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12670 12670 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502208389 : ℝ) ≤ plow 12670 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.561094522041 : ℝ) ≤ √(12670 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12670 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12670 Θ 1.22 ≤ 0.011781162094 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.561094522041 := by gcongr <;> linarith
      _ ≤ (0.011781162094 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12670 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12670 12670 0.011 ≤ 0.008492161896 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12670 12670 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12670 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12670 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12670 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12670 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162436252276 + 0.011781162094 + (0.008492161896 : ℝ) *
        (1 + 2 * (0.282283742757 + 0.011781162094) / (0.560502208389 * 112.561094522041))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12670]

end BstLean.Part269.N12670

/-! The original eight local profiles supply actual 12670 moment certificates. -/
namespace BstLean.Part269.N12670
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12670 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12670 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12670 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052778931296 ∧
    0 ≤ bN 12670 BstLean.Part154.csC (groupTheta g) ∧ bN 12670 BstLean.Part154.csC (groupTheta g) ≤ 0.001383758105 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12670 12670 0.011
      (momentAllowance 12670 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12670 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12670 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12670 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12670 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12670 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229736656405 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12670 0.011
      (momentAllowance 12670 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12670 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12670
/-! The actual computed-centre upper energy formula at 12670. -/
namespace BstLean.Part269.N12670
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12670

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12670
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12670)
open BstLean.Part268 (cell12670)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085578237812
  | 2 => 0.086522614716
  | 3 => 0.087465370501
  | 4 => 0.088407978213
  | 5 => 0.089352217745
  | 6 => 0.090300221174
  | 7 => 0.091254522316
  | 8 => 0.092218110546
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12670 12670 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12670 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12670

/-! Actual upper energy certificates on all 43 source endpoints at 12670. -/
namespace BstLean.Part269.N12670
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12670)
open BstLean.Part268 (cell12670)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12670 (gMinus 12670) (1 - (cell12670 i).lower) ≤ 1 ∧
    energyUpper 12670 (gMinus 12670) (BstLean.Part211.gPlus 12670)
      (finiteEnergy 12670 12670 0.011) (1 - (cell12670 i).lower) ≤
      (cell12670 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨10,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨11,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨12,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨13,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨14,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨15,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨16,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨17,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨18,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨19,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨20,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨21,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨22,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨23,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨24,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨25,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨26,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨27,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨28,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨29,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨30,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨31,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨32,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨33,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨34,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨35,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨36,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨37,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨38,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨39,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨40,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨41,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨42,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨43,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨44,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨45,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨46,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨47,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨48,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨49,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨50,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨51,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12670) (by norm_num)
        (q := 1 - (cell12670 ⟨52,by decide⟩).lower)
        (by norm_num [cell12670]) (by norm_num [cell12670])
      exact ⟨E.1,E.2.trans (by norm_num [cell12670])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12670

/-! Source-cell containment and simple scalar guards at 12670. -/
namespace BstLean.Part269.N12670
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12670)
open BstLean.Part268 (cell12670)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12670 ⟨10,by decide⟩).lower ∧ (cell12670 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12670 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12670 ⟨11,by decide⟩).lower ∧ (cell12670 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12670 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12670 ⟨12,by decide⟩).lower ∧ (cell12670 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12670 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12670 ⟨13,by decide⟩).lower ∧ (cell12670 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12670 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12670 ⟨14,by decide⟩).lower ∧ (cell12670 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12670 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12670 ⟨15,by decide⟩).lower ∧ (cell12670 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12670 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12670 ⟨16,by decide⟩).lower ∧ (cell12670 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12670 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12670 ⟨17,by decide⟩).lower ∧ (cell12670 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12670 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12670 ⟨18,by decide⟩).lower ∧ (cell12670 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12670 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12670 ⟨19,by decide⟩).lower ∧ (cell12670 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12670 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12670 ⟨20,by decide⟩).lower ∧ (cell12670 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12670 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12670 ⟨21,by decide⟩).lower ∧ (cell12670 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12670 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12670 ⟨22,by decide⟩).lower ∧ (cell12670 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12670 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12670 ⟨23,by decide⟩).lower ∧ (cell12670 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12670 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12670 ⟨24,by decide⟩).lower ∧ (cell12670 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12670 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12670 ⟨25,by decide⟩).lower ∧ (cell12670 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12670 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12670 ⟨26,by decide⟩).lower ∧ (cell12670 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12670 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12670 ⟨27,by decide⟩).lower ∧ (cell12670 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12670 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12670 ⟨28,by decide⟩).lower ∧ (cell12670 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12670 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12670 ⟨29,by decide⟩).lower ∧ (cell12670 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12670 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12670 ⟨30,by decide⟩).lower ∧ (cell12670 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12670 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12670 ⟨31,by decide⟩).lower ∧ (cell12670 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12670 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12670 ⟨32,by decide⟩).lower ∧ (cell12670 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12670 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12670 ⟨33,by decide⟩).lower ∧ (cell12670 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12670 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12670 ⟨34,by decide⟩).lower ∧ (cell12670 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12670 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12670 ⟨35,by decide⟩).lower ∧ (cell12670 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12670 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12670 ⟨36,by decide⟩).lower ∧ (cell12670 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12670 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12670 ⟨37,by decide⟩).lower ∧ (cell12670 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12670 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12670 ⟨38,by decide⟩).lower ∧ (cell12670 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12670 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12670 ⟨39,by decide⟩).lower ∧ (cell12670 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12670 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12670 ⟨40,by decide⟩).lower ∧ (cell12670 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12670 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12670 ⟨41,by decide⟩).lower ∧ (cell12670 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12670 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12670 ⟨42,by decide⟩).lower ∧ (cell12670 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12670 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12670 ⟨43,by decide⟩).lower ∧ (cell12670 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12670 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12670 ⟨44,by decide⟩).lower ∧ (cell12670 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12670 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12670 ⟨45,by decide⟩).lower ∧ (cell12670 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12670 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12670 ⟨46,by decide⟩).lower ∧ (cell12670 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12670 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12670 ⟨47,by decide⟩).lower ∧ (cell12670 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12670 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12670 ⟨48,by decide⟩).lower ∧ (cell12670 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12670 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12670 ⟨49,by decide⟩).lower ∧ (cell12670 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12670 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12670 ⟨50,by decide⟩).lower ∧ (cell12670 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12670 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12670 ⟨51,by decide⟩).lower ∧ (cell12670 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12670 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12670 ⟨52,by decide⟩).lower ∧ (cell12670 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12670 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12670 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12670 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12670,cell12670,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12670 i).lower ∧
    (cell12670 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12670 i).upper ≤ (0.532 : ℝ) ∧
    (cell12670 i).centre ≤ (0.1 : ℝ) ∧ (cell12670 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12670 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12670 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12670

/-! The local source numeric instances at 12670 have no network premises. -/
namespace BstLean.Part269.N12670
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12670)
open BstLean.Part268 (cell12670)

noncomputable def sourceNumerics12670 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12670 (cell12670 i)
      scalarRow12670.M scalarRow12670.H scalarRow12670.xi := by
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
    energy_allowance := scalarRow12670.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12670]
    centre_nonneg := (scalarRow12670.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12670])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12670
/-! Actual 12671 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12671
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12671 ≤ (1.035850536333 : ℝ) := by
  have hr : (112.565536466540 : ℝ) ≤ √(12671 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.565536466540 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12671 12671 (11 / 1000) ≤
    (0.008491826784 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12671) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.565536466540 : ℝ) ≤ √(12671 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12671)
  have hdiv : K / √(12671 : ℝ) ≤ K / 112.565536466540 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.565536466540 ≤ (0.008491826784 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12671.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12671 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12671 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12671 := gPlus_lower 12671
end BstLean.Part269.N12671

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12671
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035850536332 : ℝ) ≤ wn 12671 := by
  have hn : √(12671 : ℝ) ≤ 112.565536466541 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12671 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.565536466541 ≤ 2 / √(12671 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252467416 : ℝ) ≤ rhoBar 12671 BstLean.Part154.csC ∧
    rhoBar 12671 BstLean.Part154.csC ≤ 0.000252467807 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035850536332 : ℝ) / (1.295212 * 12671) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035850536333 : ℝ) / (1.29521 * 12671) := by gcongr
      _ ≤ (0.000252467807 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12671 BstLean.Part154.csC) ≤ 0.001009934968 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12671 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12671 BstLean.Part154.csC) (piBar (rhoBar 12671 BstLean.Part154.csC)) ≤ 0.000192836635 ∧
    cc1 (rhoBar 12671 BstLean.Part154.csC) (piBar (rhoBar 12671 BstLean.Part154.csC)) ≤ 0.000122703227 ∧
    cc2 (rhoBar 12671 BstLean.Part154.csC) ≤ 0.000071230158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12671 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12671 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12671 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12671 BstLean.Part154.csC * nuR (rhoBar 12671 BstLean.Part154.csC)) ≤ 0.000504951549 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252467807 : ℝ) * 0.001009934968 := by gcongr
      _ ≤ (0.000504951549 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12671 BstLean.Part154.csC) * nuR (rhoBar 12671 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001009934968 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12671 BstLean.Part154.csC) * rhoBar 12671 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252467807 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252467807 / 2 + 0.399 * 0.001009934968 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192836635 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504951549 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122703227 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252467807 / 1.414213562 := by gcongr
      _ ≤ (0.000071230158 : ℝ) := by norm_num

end BstLean.Part269.N12671

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12671
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12671 BstLean.Part154.csC) (piBar (rhoBar 12671 BstLean.Part154.csC)) ≤ 1.60589E-7 := by
  have hr0 : 0 ≤ rhoBar 12671 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12671 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12671 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12671 BstLean.Part154.csC) (piBar (rhoBar 12671 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12671 BstLean.Part154.csC) (piBar (rhoBar 12671 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12671 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192836635 : ℝ) ^ 2 + 0.000122703227 ^ 2 + 3 * 0.000071230158 ^ 2 +
        2 * 0.797885 * 0.000192836635 * 0.000122703227 + 2 * 0.000192836635 * 0.000071230158 +
        4 * 0.797885 * 0.000122703227 * 0.000071230158 := by gcongr
    _ ≤ (1.60589E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12671 BstLean.Part154.csC Θ ≤ 0.002635527458 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12671 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12671 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12671 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12671 BstLean.Part154.csC) (piBar (rhoBar 12671 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12671 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035850536333 * 1.60589E-7 / (0.000252467416 : ℝ) := by gcongr
    _ ≤ 0.002635527458 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12671 BstLean.Part154.csC Θ ≤ 0.002924365228 + 0.000665952583 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12671 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12671 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12671 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035850536333 : ℝ) * ((2 * Θ * 0.000252467807 +
        (6863 / 10000) * 0.000252467807 * 12671 * 0.001009934968) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002924365228 + 0.000665952583 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12671 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12671 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12671 0.011 Θ ∧ gammaRatio 12671 0.011 Θ ≤ 0.000086791904 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12671 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035850536333 : ℝ) * 0.525 / ((1 - 0.011) * 12671) := by gcongr
      _ ≤ (0.000086791904 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12671 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12671 0.011 Θ) :=
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
    badAllowance 12671 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12671 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12671 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12671 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12671 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12671 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12671 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12671 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12671 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12671 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12671 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035850536333 : ℝ) * 12671 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12671 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003538676619 + 0.003301480041 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12671

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12671
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12671 BstLean.Part154.csC) (piBar (rhoBar 12671 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12671 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12671 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12671 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12671 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12671 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12671 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12671 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12671 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12671 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12671 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12671 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12671 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12671 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12671 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052544990285 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12671) ≤ 0.010609264777 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12671 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035850536333)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010609264777 + 2 * 0.737676 / 12671) := by gcongr
    _ ≤ (0.052544990285 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12671 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12671

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12671
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502253823 : ℝ) ≤ plow 12671 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12671) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052778553641)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383651916) : eMP 12671 0.011 xi bn ≤ 0.001191148501 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12671 : ℝ) * (1 - 0.011))) ≤ 0.000588958635 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001383651916 / (12671 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588958635 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588958635 : ℝ) + 3.141593 * 0.052778553641 / (12671 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001191148501 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052778553641)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383651916) : PiBarMP 12671 12 0.011 xi bn ≤ 0.161437241791 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12671 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037197471904 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.944714033311 : ℝ) ≤ √((12671 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.565536466540 : ℝ) ≤ √(12671 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12671) ≤ 0.123771526349 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037197471904 + 0.052778553641 * 1.772454 / (2 * (111.944714033311 : ℝ))) * (1 + 0.001191148501) +
        8 / (12671 * 112.565536466540) + 0.123771526349 := by gcongr
    _ ≤ (0.161437241791 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052778553641)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383651916) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282280824758) :
    parallelOracle 12671 0.011 xi bn cd ≤ 0.162429845024 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12671 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12671 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502253823 : ℝ) ≤ plow 12671 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.565536466540 : ℝ) ≤ √(12671 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282280824758 : ℝ) / (2 * 0.560502253823 * 112.565536466540)) * 0.161437241791 +
        0.282280824758 ^ 2 / (2 * 0.560502253823 * 112.565536466540) := by gcongr
    _ ≤ (0.162429845024 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052778553641) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383651916)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282280824758) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12671 12671 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502253823 : ℝ) ≤ plow 12671 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.565536466540 : ℝ) ≤ √(12671 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12671 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12671 Θ 1.22 ≤ 0.011780697198 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.565536466540 := by gcongr <;> linarith
      _ ≤ (0.011780697198 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12671 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12671 12671 0.011 ≤ 0.008491826784 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12671 12671 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12671 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12671 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12671 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12671 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162429845024 + 0.011780697198 + (0.008491826784 : ℝ) *
        (1 + 2 * (0.282280824758 + 0.011780697198) / (0.560502253823 * 112.565536466540))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12671]

end BstLean.Part269.N12671

/-! The original eight local profiles supply actual 12671 moment certificates. -/
namespace BstLean.Part269.N12671
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12671 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12671 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12671 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052778553641 ∧
    0 ≤ bN 12671 BstLean.Part154.csC (groupTheta g) ∧ bN 12671 BstLean.Part154.csC (groupTheta g) ≤ 0.001383651916 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12671 12671 0.011
      (momentAllowance 12671 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12671 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12671 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12671 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12671 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12671 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229735834473 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12671 0.011
      (momentAllowance 12671 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12671 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12671
/-! The actual computed-centre upper energy formula at 12671. -/
namespace BstLean.Part269.N12671
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12671

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12671
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12671)
open BstLean.Part268 (cell12671)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085575289057
  | 2 => 0.086519611045
  | 3 => 0.087462303782
  | 4 => 0.088404838453
  | 5 => 0.089348992756
  | 6 => 0.090296896209
  | 7 => 0.091251079657
  | 8 => 0.092214529049
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12671 12671 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12671 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12671

/-! Actual upper energy certificates on all 43 source endpoints at 12671. -/
namespace BstLean.Part269.N12671
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12671)
open BstLean.Part268 (cell12671)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12671 (gMinus 12671) (1 - (cell12671 i).lower) ≤ 1 ∧
    energyUpper 12671 (gMinus 12671) (BstLean.Part211.gPlus 12671)
      (finiteEnergy 12671 12671 0.011) (1 - (cell12671 i).lower) ≤
      (cell12671 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨10,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨11,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨12,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨13,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨14,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨15,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨16,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨17,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨18,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨19,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨20,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨21,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨22,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨23,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨24,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨25,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨26,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨27,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨28,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨29,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨30,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨31,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨32,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨33,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨34,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨35,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨36,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨37,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨38,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨39,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨40,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨41,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨42,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨43,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨44,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨45,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨46,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨47,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨48,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨49,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨50,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨51,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12671) (by norm_num)
        (q := 1 - (cell12671 ⟨52,by decide⟩).lower)
        (by norm_num [cell12671]) (by norm_num [cell12671])
      exact ⟨E.1,E.2.trans (by norm_num [cell12671])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12671

/-! Source-cell containment and simple scalar guards at 12671. -/
namespace BstLean.Part269.N12671
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12671)
open BstLean.Part268 (cell12671)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12671 ⟨10,by decide⟩).lower ∧ (cell12671 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12671 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12671 ⟨11,by decide⟩).lower ∧ (cell12671 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12671 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12671 ⟨12,by decide⟩).lower ∧ (cell12671 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12671 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12671 ⟨13,by decide⟩).lower ∧ (cell12671 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12671 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12671 ⟨14,by decide⟩).lower ∧ (cell12671 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12671 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12671 ⟨15,by decide⟩).lower ∧ (cell12671 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12671 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12671 ⟨16,by decide⟩).lower ∧ (cell12671 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12671 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12671 ⟨17,by decide⟩).lower ∧ (cell12671 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12671 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12671 ⟨18,by decide⟩).lower ∧ (cell12671 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12671 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12671 ⟨19,by decide⟩).lower ∧ (cell12671 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12671 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12671 ⟨20,by decide⟩).lower ∧ (cell12671 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12671 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12671 ⟨21,by decide⟩).lower ∧ (cell12671 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12671 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12671 ⟨22,by decide⟩).lower ∧ (cell12671 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12671 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12671 ⟨23,by decide⟩).lower ∧ (cell12671 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12671 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12671 ⟨24,by decide⟩).lower ∧ (cell12671 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12671 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12671 ⟨25,by decide⟩).lower ∧ (cell12671 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12671 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12671 ⟨26,by decide⟩).lower ∧ (cell12671 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12671 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12671 ⟨27,by decide⟩).lower ∧ (cell12671 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12671 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12671 ⟨28,by decide⟩).lower ∧ (cell12671 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12671 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12671 ⟨29,by decide⟩).lower ∧ (cell12671 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12671 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12671 ⟨30,by decide⟩).lower ∧ (cell12671 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12671 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12671 ⟨31,by decide⟩).lower ∧ (cell12671 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12671 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12671 ⟨32,by decide⟩).lower ∧ (cell12671 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12671 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12671 ⟨33,by decide⟩).lower ∧ (cell12671 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12671 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12671 ⟨34,by decide⟩).lower ∧ (cell12671 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12671 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12671 ⟨35,by decide⟩).lower ∧ (cell12671 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12671 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12671 ⟨36,by decide⟩).lower ∧ (cell12671 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12671 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12671 ⟨37,by decide⟩).lower ∧ (cell12671 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12671 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12671 ⟨38,by decide⟩).lower ∧ (cell12671 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12671 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12671 ⟨39,by decide⟩).lower ∧ (cell12671 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12671 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12671 ⟨40,by decide⟩).lower ∧ (cell12671 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12671 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12671 ⟨41,by decide⟩).lower ∧ (cell12671 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12671 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12671 ⟨42,by decide⟩).lower ∧ (cell12671 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12671 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12671 ⟨43,by decide⟩).lower ∧ (cell12671 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12671 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12671 ⟨44,by decide⟩).lower ∧ (cell12671 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12671 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12671 ⟨45,by decide⟩).lower ∧ (cell12671 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12671 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12671 ⟨46,by decide⟩).lower ∧ (cell12671 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12671 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12671 ⟨47,by decide⟩).lower ∧ (cell12671 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12671 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12671 ⟨48,by decide⟩).lower ∧ (cell12671 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12671 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12671 ⟨49,by decide⟩).lower ∧ (cell12671 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12671 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12671 ⟨50,by decide⟩).lower ∧ (cell12671 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12671 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12671 ⟨51,by decide⟩).lower ∧ (cell12671 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12671 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12671 ⟨52,by decide⟩).lower ∧ (cell12671 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12671 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12671 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12671 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12671,cell12671,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12671 i).lower ∧
    (cell12671 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12671 i).upper ≤ (0.532 : ℝ) ∧
    (cell12671 i).centre ≤ (0.1 : ℝ) ∧ (cell12671 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12671 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12671 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12671

/-! The local source numeric instances at 12671 have no network premises. -/
namespace BstLean.Part269.N12671
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12671)
open BstLean.Part268 (cell12671)

noncomputable def sourceNumerics12671 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12671 (cell12671 i)
      scalarRow12671.M scalarRow12671.H scalarRow12671.xi := by
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
    energy_allowance := scalarRow12671.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12671]
    centre_nonneg := (scalarRow12671.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12671])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12671
/-! Actual 12672 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12672
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12672 ≤ (1.035849109292 : ℝ) := by
  have hr : (112.569978235762 : ℝ) ≤ √(12672 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.569978235762 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12672 12672 (11 / 1000) ≤
    (0.008491491712 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12672) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.569978235762 : ℝ) ≤ √(12672 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12672)
  have hdiv : K / √(12672 : ℝ) ≤ K / 112.569978235762 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.569978235762 ≤ (0.008491491712 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12672.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12672 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12672 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12672 := gPlus_lower 12672
end BstLean.Part269.N12672

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12672
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035849109291 : ℝ) ≤ wn 12672 := by
  have hn : √(12672 : ℝ) ≤ 112.569978235763 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12672 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.569978235763 ≤ 2 / √(12672 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252447145 : ℝ) ≤ rhoBar 12672 BstLean.Part154.csC ∧
    rhoBar 12672 BstLean.Part154.csC ≤ 0.000252447536 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035849109291 : ℝ) / (1.295212 * 12672) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035849109292 : ℝ) / (1.29521 * 12672) := by gcongr
      _ ≤ (0.000252447536 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12672 BstLean.Part154.csC) ≤ 0.001009853874 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12672 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12672 BstLean.Part154.csC) (piBar (rhoBar 12672 BstLean.Part154.csC)) ≤ 0.000192821151 ∧
    cc1 (rhoBar 12672 BstLean.Part154.csC) (piBar (rhoBar 12672 BstLean.Part154.csC)) ≤ 0.000122693375 ∧
    cc2 (rhoBar 12672 BstLean.Part154.csC) ≤ 0.000071224439 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12672 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12672 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12672 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12672 BstLean.Part154.csC * nuR (rhoBar 12672 BstLean.Part154.csC)) ≤ 0.000504911005 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252447536 : ℝ) * 0.001009853874 := by gcongr
      _ ≤ (0.000504911005 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12672 BstLean.Part154.csC) * nuR (rhoBar 12672 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001009853874 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12672 BstLean.Part154.csC) * rhoBar 12672 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252447536 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252447536 / 2 + 0.399 * 0.001009853874 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192821151 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504911005 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122693375 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252447536 / 1.414213562 := by gcongr
      _ ≤ (0.000071224439 : ℝ) := by norm_num

end BstLean.Part269.N12672

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12672
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12672 BstLean.Part154.csC) (piBar (rhoBar 12672 BstLean.Part154.csC)) ≤ 1.60563E-7 := by
  have hr0 : 0 ≤ rhoBar 12672 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12672 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12672 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12672 BstLean.Part154.csC) (piBar (rhoBar 12672 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12672 BstLean.Part154.csC) (piBar (rhoBar 12672 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12672 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192821151 : ℝ) ^ 2 + 0.000122693375 ^ 2 + 3 * 0.000071224439 ^ 2 +
        2 * 0.797885 * 0.000192821151 * 0.000122693375 + 2 * 0.000192821151 * 0.000071224439 +
        4 * 0.797885 * 0.000122693375 * 0.000071224439 := by gcongr
    _ ≤ (1.60563E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12672 BstLean.Part154.csC Θ ≤ 0.002635308719 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12672 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12672 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12672 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12672 BstLean.Part154.csC) (piBar (rhoBar 12672 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12672 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035849109292 * 1.60563E-7 / (0.000252447145 : ℝ) := by gcongr
    _ ≤ 0.002635308719 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12672 BstLean.Part154.csC Θ ≤ 0.002924122356 + 0.000665898196 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12672 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12672 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12672 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035849109292 : ℝ) * ((2 * Θ * 0.000252447536 +
        (6863 / 10000) * 0.000252447536 * 12672 * 0.001009853874) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002924122356 + 0.000665898196 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12672 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12672 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12672 0.011 Θ ∧ gammaRatio 12672 0.011 Θ ≤ 0.000086784935 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12672 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035849109292 : ℝ) * 0.525 / ((1 - 0.011) * 12672) := by gcongr
      _ ≤ (0.000086784935 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12672 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12672 0.011 Θ) :=
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
    badAllowance 12672 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12672 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12672 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12672 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12672 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12672 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12672 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12672 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12672 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12672 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12672 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035849109292 : ℝ) * 12672 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12672 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003538433747 + 0.003301206915 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12672

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12672
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12672 BstLean.Part154.csC) (piBar (rhoBar 12672 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12672 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12672 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12672 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12672 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12672 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12672 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12672 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12672 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12672 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12672 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12672 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12672 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12672 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12672 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052542894465 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12672) ≤ 0.010608846158 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12672 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035849109292)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010608846158 + 2 * 0.737676 / 12672) := by gcongr
    _ ≤ (0.052542894465 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12672 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12672

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12672
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502299250 : ℝ) ≤ plow 12672 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12672) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052778167378)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383537078) : eMP 12672 0.011 xi bn ≤ 0.001191052002 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12672 : ℝ) * (1 - 0.011))) ≤ 0.000588910956 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001383537078 / (12672 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588910956 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588910956 : ℝ) + 3.141593 * 0.052778167378 / (12672 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001191052002 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052778167378)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383537078) : PiBarMP 12672 12 0.011 xi bn ≤ 0.161430788674 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12672 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037195928245 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.949131305249 : ℝ) ≤ √((12672 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.569978235762 : ℝ) ≤ √(12672 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12672) ≤ 0.123766642591 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037195928245 + 0.052778167378 * 1.772454 / (2 * (111.949131305249 : ℝ))) * (1 + 0.001191052002) +
        8 / (12672 * 112.569978235762) + 0.123766642591 := by gcongr
    _ ≤ (0.161430788674 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052778167378)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383537078) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282277888269) :
    parallelOracle 12672 0.011 xi bn cd ≤ 0.162423321332 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12672 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12672 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502299250 : ℝ) ≤ plow 12672 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.569978235762 : ℝ) ≤ √(12672 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282277888269 : ℝ) / (2 * 0.560502299250 * 112.569978235762)) * 0.161430788674 +
        0.282277888269 ^ 2 / (2 * 0.560502299250 * 112.569978235762) := by gcongr
    _ ≤ (0.162423321332 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052778167378) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383537078)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282277888269) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12672 12672 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502299250 : ℝ) ≤ plow 12672 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.569978235762 : ℝ) ≤ √(12672 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12672 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12672 Θ 1.22 ≤ 0.011780232357 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.569978235762 := by gcongr <;> linarith
      _ ≤ (0.011780232357 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12672 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12672 12672 0.011 ≤ 0.008491491712 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12672 12672 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12672 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12672 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12672 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12672 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162423321332 + 0.011780232357 + (0.008491491712 : ℝ) *
        (1 + 2 * (0.282277888269 + 0.011780232357) / (0.560502299250 * 112.569978235762))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12672]

end BstLean.Part269.N12672

/-! The original eight local profiles supply actual 12672 moment certificates. -/
namespace BstLean.Part269.N12672
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12672 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12672 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12672 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052778167378 ∧
    0 ≤ bN 12672 BstLean.Part154.csC (groupTheta g) ∧ bN 12672 BstLean.Part154.csC (groupTheta g) ≤ 0.001383537078 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12672 12672 0.011
      (momentAllowance 12672 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12672 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12672 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12672 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12672 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12672 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229734993804 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12672 0.011
      (momentAllowance 12672 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12672 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12672
/-! The actual computed-centre upper energy formula at 12672. -/
namespace BstLean.Part269.N12672
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12672

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12672
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12672)
open BstLean.Part268 (cell12672)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085572341419
  | 2 => 0.086516608536
  | 3 => 0.087459238284
  | 4 => 0.088401699982
  | 5 => 0.089345769143
  | 6 => 0.090293572723
  | 7 => 0.091247638604
  | 8 => 0.092210949309
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12672 12672 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12672 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12672

/-! Actual upper energy certificates on all 43 source endpoints at 12672. -/
namespace BstLean.Part269.N12672
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12672)
open BstLean.Part268 (cell12672)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12672 (gMinus 12672) (1 - (cell12672 i).lower) ≤ 1 ∧
    energyUpper 12672 (gMinus 12672) (BstLean.Part211.gPlus 12672)
      (finiteEnergy 12672 12672 0.011) (1 - (cell12672 i).lower) ≤
      (cell12672 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨10,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨11,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨12,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨13,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨14,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨15,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨16,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨17,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨18,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨19,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨20,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨21,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨22,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨23,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨24,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨25,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨26,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨27,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨28,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨29,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨30,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨31,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨32,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨33,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨34,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨35,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨36,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨37,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨38,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨39,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨40,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨41,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨42,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨43,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨44,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨45,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨46,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨47,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨48,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨49,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨50,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨51,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12672) (by norm_num)
        (q := 1 - (cell12672 ⟨52,by decide⟩).lower)
        (by norm_num [cell12672]) (by norm_num [cell12672])
      exact ⟨E.1,E.2.trans (by norm_num [cell12672])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12672

/-! Source-cell containment and simple scalar guards at 12672. -/
namespace BstLean.Part269.N12672
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12672)
open BstLean.Part268 (cell12672)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12672 ⟨10,by decide⟩).lower ∧ (cell12672 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12672 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12672 ⟨11,by decide⟩).lower ∧ (cell12672 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12672 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12672 ⟨12,by decide⟩).lower ∧ (cell12672 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12672 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12672 ⟨13,by decide⟩).lower ∧ (cell12672 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12672 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12672 ⟨14,by decide⟩).lower ∧ (cell12672 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12672 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12672 ⟨15,by decide⟩).lower ∧ (cell12672 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12672 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12672 ⟨16,by decide⟩).lower ∧ (cell12672 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12672 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12672 ⟨17,by decide⟩).lower ∧ (cell12672 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12672 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12672 ⟨18,by decide⟩).lower ∧ (cell12672 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12672 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12672 ⟨19,by decide⟩).lower ∧ (cell12672 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12672 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12672 ⟨20,by decide⟩).lower ∧ (cell12672 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12672 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12672 ⟨21,by decide⟩).lower ∧ (cell12672 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12672 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12672 ⟨22,by decide⟩).lower ∧ (cell12672 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12672 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12672 ⟨23,by decide⟩).lower ∧ (cell12672 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12672 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12672 ⟨24,by decide⟩).lower ∧ (cell12672 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12672 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12672 ⟨25,by decide⟩).lower ∧ (cell12672 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12672 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12672 ⟨26,by decide⟩).lower ∧ (cell12672 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12672 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12672 ⟨27,by decide⟩).lower ∧ (cell12672 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12672 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12672 ⟨28,by decide⟩).lower ∧ (cell12672 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12672 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12672 ⟨29,by decide⟩).lower ∧ (cell12672 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12672 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12672 ⟨30,by decide⟩).lower ∧ (cell12672 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12672 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12672 ⟨31,by decide⟩).lower ∧ (cell12672 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12672 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12672 ⟨32,by decide⟩).lower ∧ (cell12672 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12672 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12672 ⟨33,by decide⟩).lower ∧ (cell12672 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12672 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12672 ⟨34,by decide⟩).lower ∧ (cell12672 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12672 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12672 ⟨35,by decide⟩).lower ∧ (cell12672 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12672 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12672 ⟨36,by decide⟩).lower ∧ (cell12672 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12672 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12672 ⟨37,by decide⟩).lower ∧ (cell12672 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12672 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12672 ⟨38,by decide⟩).lower ∧ (cell12672 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12672 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12672 ⟨39,by decide⟩).lower ∧ (cell12672 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12672 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12672 ⟨40,by decide⟩).lower ∧ (cell12672 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12672 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12672 ⟨41,by decide⟩).lower ∧ (cell12672 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12672 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12672 ⟨42,by decide⟩).lower ∧ (cell12672 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12672 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12672 ⟨43,by decide⟩).lower ∧ (cell12672 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12672 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12672 ⟨44,by decide⟩).lower ∧ (cell12672 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12672 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12672 ⟨45,by decide⟩).lower ∧ (cell12672 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12672 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12672 ⟨46,by decide⟩).lower ∧ (cell12672 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12672 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12672 ⟨47,by decide⟩).lower ∧ (cell12672 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12672 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12672 ⟨48,by decide⟩).lower ∧ (cell12672 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12672 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12672 ⟨49,by decide⟩).lower ∧ (cell12672 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12672 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12672 ⟨50,by decide⟩).lower ∧ (cell12672 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12672 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12672 ⟨51,by decide⟩).lower ∧ (cell12672 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12672 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12672 ⟨52,by decide⟩).lower ∧ (cell12672 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12672 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12672 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12672 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12672,cell12672,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12672 i).lower ∧
    (cell12672 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12672 i).upper ≤ (0.532 : ℝ) ∧
    (cell12672 i).centre ≤ (0.1 : ℝ) ∧ (cell12672 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12672 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12672 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12672

/-! The local source numeric instances at 12672 have no network premises. -/
namespace BstLean.Part269.N12672
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12672)
open BstLean.Part268 (cell12672)

noncomputable def sourceNumerics12672 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12672 (cell12672 i)
      scalarRow12672.M scalarRow12672.H scalarRow12672.xi := by
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
    energy_allowance := scalarRow12672.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12672]
    centre_nonneg := (scalarRow12672.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12672])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12672
/-! Actual 12673 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12673
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12673 ≤ (1.035847682421 : ℝ) := by
  have hr : (112.574419829728 : ℝ) ≤ √(12673 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.574419829728 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12673 12673 (11 / 1000) ≤
    (0.008491156680 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12673) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.574419829728 : ℝ) ≤ √(12673 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12673)
  have hdiv : K / √(12673 : ℝ) ≤ K / 112.574419829728 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.574419829728 ≤ (0.008491156680 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12673.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12673 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12673 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12673 := gPlus_lower 12673
end BstLean.Part269.N12673

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12673
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035847682420 : ℝ) ≤ wn 12673 := by
  have hn : √(12673 : ℝ) ≤ 112.574419829729 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12673 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.574419829729 ≤ 2 / √(12673 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252426877 : ℝ) ≤ rhoBar 12673 BstLean.Part154.csC ∧
    rhoBar 12673 BstLean.Part154.csC ≤ 0.000252427268 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035847682420 : ℝ) / (1.295212 * 12673) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035847682421 : ℝ) / (1.29521 * 12673) := by gcongr
      _ ≤ (0.000252427268 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12673 BstLean.Part154.csC) ≤ 0.001009772792 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12673 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12673 BstLean.Part154.csC) (piBar (rhoBar 12673 BstLean.Part154.csC)) ≤ 0.000192805670 ∧
    cc1 (rhoBar 12673 BstLean.Part154.csC) (piBar (rhoBar 12673 BstLean.Part154.csC)) ≤ 0.000122683524 ∧
    cc2 (rhoBar 12673 BstLean.Part154.csC) ≤ 0.000071218721 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12673 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12673 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12673 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12673 BstLean.Part154.csC * nuR (rhoBar 12673 BstLean.Part154.csC)) ≤ 0.000504870466 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252427268 : ℝ) * 0.001009772792 := by gcongr
      _ ≤ (0.000504870466 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12673 BstLean.Part154.csC) * nuR (rhoBar 12673 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001009772792 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12673 BstLean.Part154.csC) * rhoBar 12673 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252427268 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252427268 / 2 + 0.399 * 0.001009772792 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192805670 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504870466 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122683524 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252427268 / 1.414213562 := by gcongr
      _ ≤ (0.000071218721 : ℝ) := by norm_num

end BstLean.Part269.N12673

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12673
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12673 BstLean.Part154.csC) (piBar (rhoBar 12673 BstLean.Part154.csC)) ≤ 1.60537E-7 := by
  have hr0 : 0 ≤ rhoBar 12673 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12673 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12673 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12673 BstLean.Part154.csC) (piBar (rhoBar 12673 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12673 BstLean.Part154.csC) (piBar (rhoBar 12673 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12673 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192805670 : ℝ) ^ 2 + 0.000122683524 ^ 2 + 3 * 0.000071218721 ^ 2 +
        2 * 0.797885 * 0.000192805670 * 0.000122683524 + 2 * 0.000192805670 * 0.000071218721 +
        4 * 0.797885 * 0.000122683524 * 0.000071218721 := by gcongr
    _ ≤ (1.60537E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12673 BstLean.Part154.csC Θ ≤ 0.002635089914 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12673 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12673 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12673 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12673 BstLean.Part154.csC) (piBar (rhoBar 12673 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12673 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035847682421 * 1.60537E-7 / (0.000252426877 : ℝ) := by gcongr
    _ ≤ 0.002635089914 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12673 BstLean.Part154.csC Θ ≤ 0.002923879519 + 0.000665843816 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12673 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12673 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12673 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035847682421 : ℝ) * ((2 * Θ * 0.000252427268 +
        (6863 / 10000) * 0.000252427268 * 12673 * 0.001009772792) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002923879519 + 0.000665843816 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12673 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12673 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12673 0.011 Θ ∧ gammaRatio 12673 0.011 Θ ≤ 0.000086777967 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12673 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035847682421 : ℝ) * 0.525 / ((1 - 0.011) * 12673) := by gcongr
      _ ≤ (0.000086777967 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12673 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12673 0.011 Θ) :=
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
    badAllowance 12673 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12673 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12673 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12673 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12673 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12673 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12673 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12673 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12673 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12673 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12673 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035847682421 : ℝ) * 12673 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12673 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003538190910 + 0.003300933730 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12673

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12673
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12673 BstLean.Part154.csC) (piBar (rhoBar 12673 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12673 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12673 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12673 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12673 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12673 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12673 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12673 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12673 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12673 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12673 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12673 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12673 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12673 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12673 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052540798897 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12673) ≤ 0.010608427589 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12673 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035847682421)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010608427589 + 2 * 0.737676 / 12673) := by gcongr
    _ ≤ (0.052540798897 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12673 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12673

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12673
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502344669 : ℝ) ≤ plow 12673 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12673) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052777781119)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383422205) : eMP 12673 0.011 xi bn ≤ 0.001190955495 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12673 : ℝ) * (1 - 0.011))) ≤ 0.000588863273 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001383422205 / (12673 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588863273 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588863273 : ℝ) + 3.141593 * 0.052777781119 / (12673 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001190955495 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052777781119)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383422205) : PiBarMP 12673 12 0.011 xi bn ≤ 0.161424335602 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12673 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037194384052 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.953548402897 : ℝ) ≤ √((12673 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.574419829728 : ℝ) ≤ √(12673 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12673) ≤ 0.123761759411 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037194384052 + 0.052777781119 * 1.772454 / (2 * (111.953548402897 : ℝ))) * (1 + 0.001190955495) +
        8 / (12673 * 112.574419829728) + 0.123761759411 := by gcongr
    _ ≤ (0.161424335602 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052777781119)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383422205) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282274952038) :
    parallelOracle 12673 0.011 xi bn cd ≤ 0.162416797693 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12673 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12673 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502344669 : ℝ) ≤ plow 12673 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.574419829728 : ℝ) ≤ √(12673 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282274952038 : ℝ) / (2 * 0.560502344669 * 112.574419829728)) * 0.161424335602 +
        0.282274952038 ^ 2 / (2 * 0.560502344669 * 112.574419829728) := by gcongr
    _ ≤ (0.162416797693 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052777781119) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383422205)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282274952038) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12673 12673 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502344669 : ℝ) ≤ plow 12673 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.574419829728 : ℝ) ≤ √(12673 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12673 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12673 Θ 1.22 ≤ 0.011779767571 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.574419829728 := by gcongr <;> linarith
      _ ≤ (0.011779767571 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12673 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12673 12673 0.011 ≤ 0.008491156680 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12673 12673 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12673 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12673 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12673 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12673 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162416797693 + 0.011779767571 + (0.008491156680 : ℝ) *
        (1 + 2 * (0.282274952038 + 0.011779767571) / (0.560502344669 * 112.574419829728))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12673]

end BstLean.Part269.N12673

/-! The original eight local profiles supply actual 12673 moment certificates. -/
namespace BstLean.Part269.N12673
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12673 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12673 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12673 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052777781119 ∧
    0 ≤ bN 12673 BstLean.Part154.csC (groupTheta g) ∧ bN 12673 BstLean.Part154.csC (groupTheta g) ≤ 0.001383422205 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12673 12673 0.011
      (momentAllowance 12673 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12673 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12673 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12673 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12673 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12673 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229734153141 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12673 0.011
      (momentAllowance 12673 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12673 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12673
/-! The actual computed-centre upper energy formula at 12673. -/
namespace BstLean.Part269.N12673
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12673

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12673
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12673)
open BstLean.Part268 (cell12673)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085569394895
  | 2 => 0.086513607189
  | 3 => 0.087456174003
  | 4 => 0.088398562800
  | 5 => 0.089342546903
  | 6 => 0.090290250716
  | 7 => 0.091244199154
  | 8 => 0.092207371324
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12673 12673 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12673 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12673

/-! Actual upper energy certificates on all 43 source endpoints at 12673. -/
namespace BstLean.Part269.N12673
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12673)
open BstLean.Part268 (cell12673)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12673 (gMinus 12673) (1 - (cell12673 i).lower) ≤ 1 ∧
    energyUpper 12673 (gMinus 12673) (BstLean.Part211.gPlus 12673)
      (finiteEnergy 12673 12673 0.011) (1 - (cell12673 i).lower) ≤
      (cell12673 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨10,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨11,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨12,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨13,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨14,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨15,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨16,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨17,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨18,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨19,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨20,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨21,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨22,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨23,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨24,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨25,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨26,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨27,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨28,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨29,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨30,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨31,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨32,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨33,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨34,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨35,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨36,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨37,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨38,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨39,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨40,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨41,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨42,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨43,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨44,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨45,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨46,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨47,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨48,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨49,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨50,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨51,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12673) (by norm_num)
        (q := 1 - (cell12673 ⟨52,by decide⟩).lower)
        (by norm_num [cell12673]) (by norm_num [cell12673])
      exact ⟨E.1,E.2.trans (by norm_num [cell12673])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12673

/-! Source-cell containment and simple scalar guards at 12673. -/
namespace BstLean.Part269.N12673
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12673)
open BstLean.Part268 (cell12673)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12673 ⟨10,by decide⟩).lower ∧ (cell12673 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12673 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12673 ⟨11,by decide⟩).lower ∧ (cell12673 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12673 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12673 ⟨12,by decide⟩).lower ∧ (cell12673 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12673 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12673 ⟨13,by decide⟩).lower ∧ (cell12673 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12673 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12673 ⟨14,by decide⟩).lower ∧ (cell12673 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12673 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12673 ⟨15,by decide⟩).lower ∧ (cell12673 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12673 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12673 ⟨16,by decide⟩).lower ∧ (cell12673 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12673 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12673 ⟨17,by decide⟩).lower ∧ (cell12673 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12673 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12673 ⟨18,by decide⟩).lower ∧ (cell12673 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12673 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12673 ⟨19,by decide⟩).lower ∧ (cell12673 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12673 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12673 ⟨20,by decide⟩).lower ∧ (cell12673 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12673 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12673 ⟨21,by decide⟩).lower ∧ (cell12673 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12673 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12673 ⟨22,by decide⟩).lower ∧ (cell12673 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12673 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12673 ⟨23,by decide⟩).lower ∧ (cell12673 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12673 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12673 ⟨24,by decide⟩).lower ∧ (cell12673 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12673 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12673 ⟨25,by decide⟩).lower ∧ (cell12673 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12673 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12673 ⟨26,by decide⟩).lower ∧ (cell12673 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12673 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12673 ⟨27,by decide⟩).lower ∧ (cell12673 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12673 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12673 ⟨28,by decide⟩).lower ∧ (cell12673 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12673 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12673 ⟨29,by decide⟩).lower ∧ (cell12673 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12673 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12673 ⟨30,by decide⟩).lower ∧ (cell12673 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12673 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12673 ⟨31,by decide⟩).lower ∧ (cell12673 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12673 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12673 ⟨32,by decide⟩).lower ∧ (cell12673 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12673 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12673 ⟨33,by decide⟩).lower ∧ (cell12673 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12673 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12673 ⟨34,by decide⟩).lower ∧ (cell12673 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12673 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12673 ⟨35,by decide⟩).lower ∧ (cell12673 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12673 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12673 ⟨36,by decide⟩).lower ∧ (cell12673 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12673 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12673 ⟨37,by decide⟩).lower ∧ (cell12673 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12673 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12673 ⟨38,by decide⟩).lower ∧ (cell12673 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12673 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12673 ⟨39,by decide⟩).lower ∧ (cell12673 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12673 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12673 ⟨40,by decide⟩).lower ∧ (cell12673 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12673 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12673 ⟨41,by decide⟩).lower ∧ (cell12673 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12673 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12673 ⟨42,by decide⟩).lower ∧ (cell12673 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12673 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12673 ⟨43,by decide⟩).lower ∧ (cell12673 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12673 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12673 ⟨44,by decide⟩).lower ∧ (cell12673 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12673 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12673 ⟨45,by decide⟩).lower ∧ (cell12673 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12673 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12673 ⟨46,by decide⟩).lower ∧ (cell12673 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12673 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12673 ⟨47,by decide⟩).lower ∧ (cell12673 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12673 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12673 ⟨48,by decide⟩).lower ∧ (cell12673 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12673 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12673 ⟨49,by decide⟩).lower ∧ (cell12673 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12673 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12673 ⟨50,by decide⟩).lower ∧ (cell12673 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12673 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12673 ⟨51,by decide⟩).lower ∧ (cell12673 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12673 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12673 ⟨52,by decide⟩).lower ∧ (cell12673 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12673 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12673 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12673 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12673,cell12673,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12673 i).lower ∧
    (cell12673 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12673 i).upper ≤ (0.532 : ℝ) ∧
    (cell12673 i).centre ≤ (0.1 : ℝ) ∧ (cell12673 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12673 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12673 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12673

/-! The local source numeric instances at 12673 have no network premises. -/
namespace BstLean.Part269.N12673
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12673)
open BstLean.Part268 (cell12673)

noncomputable def sourceNumerics12673 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12673 (cell12673 i)
      scalarRow12673.M scalarRow12673.H scalarRow12673.xi := by
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
    energy_allowance := scalarRow12673.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12673]
    centre_nonneg := (scalarRow12673.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12673])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12673
/-! Actual 12674 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12674
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12674 ≤ (1.035846255720 : ℝ) := by
  have hr : (112.578861248459 : ℝ) ≤ √(12674 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.578861248459 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12674 12674 (11 / 1000) ≤
    (0.008490821688 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12674) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.578861248459 : ℝ) ≤ √(12674 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12674)
  have hdiv : K / √(12674 : ℝ) ≤ K / 112.578861248459 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.578861248459 ≤ (0.008490821688 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12674.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12674 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12674 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12674 := gPlus_lower 12674
end BstLean.Part269.N12674

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12674
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035846255719 : ℝ) ≤ wn 12674 := by
  have hn : √(12674 : ℝ) ≤ 112.578861248460 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12674 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.578861248460 ≤ 2 / √(12674 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000252406613 : ℝ) ≤ rhoBar 12674 BstLean.Part154.csC ∧
    rhoBar 12674 BstLean.Part154.csC ≤ 0.000252407004 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035846255719 : ℝ) / (1.295212 * 12674) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035846255720 : ℝ) / (1.29521 * 12674) := by gcongr
      _ ≤ (0.000252407004 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12674 BstLean.Part154.csC) ≤ 0.001009691726 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12674 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12674 BstLean.Part154.csC) (piBar (rhoBar 12674 BstLean.Part154.csC)) ≤ 0.000192790191 ∧
    cc1 (rhoBar 12674 BstLean.Part154.csC) (piBar (rhoBar 12674 BstLean.Part154.csC)) ≤ 0.000122673675 ∧
    cc2 (rhoBar 12674 BstLean.Part154.csC) ≤ 0.000071213003 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12674 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12674 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12674 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12674 BstLean.Part154.csC * nuR (rhoBar 12674 BstLean.Part154.csC)) ≤ 0.000504829936 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000252407004 : ℝ) * 0.001009691726 := by gcongr
      _ ≤ (0.000504829936 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12674 BstLean.Part154.csC) * nuR (rhoBar 12674 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001009691726 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12674 BstLean.Part154.csC) * rhoBar 12674 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000252407004 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000252407004 / 2 + 0.399 * 0.001009691726 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192790191 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000504829936 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122673675 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000252407004 / 1.414213562 := by gcongr
      _ ≤ (0.000071213003 : ℝ) := by norm_num

end BstLean.Part269.N12674

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12674
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12674 BstLean.Part154.csC) (piBar (rhoBar 12674 BstLean.Part154.csC)) ≤ 1.60511E-7 := by
  have hr0 : 0 ≤ rhoBar 12674 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12674 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12674 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12674 BstLean.Part154.csC) (piBar (rhoBar 12674 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12674 BstLean.Part154.csC) (piBar (rhoBar 12674 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12674 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192790191 : ℝ) ^ 2 + 0.000122673675 ^ 2 + 3 * 0.000071213003 ^ 2 +
        2 * 0.797885 * 0.000192790191 * 0.000122673675 + 2 * 0.000192790191 * 0.000071213003 +
        4 * 0.797885 * 0.000122673675 * 0.000071213003 := by gcongr
    _ ≤ (1.60511E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12674 BstLean.Part154.csC Θ ≤ 0.002634871035 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12674 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12674 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12674 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12674 BstLean.Part154.csC) (piBar (rhoBar 12674 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12674 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035846255720 * 1.60511E-7 / (0.000252406613 : ℝ) := by gcongr
    _ ≤ 0.002634871035 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12674 BstLean.Part154.csC Θ ≤ 0.002923636738 + 0.000665789447 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12674 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12674 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12674 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035846255720 : ℝ) * ((2 * Θ * 0.000252407004 +
        (6863 / 10000) * 0.000252407004 * 12674 * 0.001009691726) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002923636738 + 0.000665789447 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12674 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12674 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12674 0.011 Θ ∧ gammaRatio 12674 0.011 Θ ≤ 0.000086771001 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12674 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035846255720 : ℝ) * 0.525 / ((1 - 0.011) * 12674) := by gcongr
      _ ≤ (0.000086771001 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12674 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12674 0.011 Θ) :=
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
    badAllowance 12674 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000614311391 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12674 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12674 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12674 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12674 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12674 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12674 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12674 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12674 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12674 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12674 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035846255720 : ℝ) * 12674 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000614311391 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12674 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003537948129 + 0.003300660482 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12674

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12674
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12674 BstLean.Part154.csC) (piBar (rhoBar 12674 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12674 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12674 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12674 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12674 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12674 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12674 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12674 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12674 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12674 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12674 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12674 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12674 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12674 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12674 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052538703577 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12674) ≤ 0.010608009069 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12674 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035846255720)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010608009069 + 2 * 0.737676 / 12674) := by gcongr
    _ ≤ (0.052538703577 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12674 12 ≤ 0.0015 := by
  exact BstLean.Part269.S12.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12674

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12674
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560502390082 : ℝ) ≤ plow 12674 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12674) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052777394883)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383307294) : eMP 12674 0.011 xi bn ≤ 0.001190858980 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12674 : ℝ) * (1 - 0.011))) ≤ 0.000588815586 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001383307294 / (12674 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000588815586 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000588815586 : ℝ) + 3.141593 * 0.052777394883 / (12674 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001190858980 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052777394883)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383307294) : PiBarMP 12674 12 0.011 xi bn ≤ 0.161417882536 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12674 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037192839284 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.957965326277 : ℝ) ≤ √((12674 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.578861248459 : ℝ) ≤ √(12674 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12674) ≤ 0.123756876809 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037192839284 + 0.052777394883 * 1.772454 / (2 * (111.957965326277 : ℝ))) * (1 + 0.001190858980) +
        8 / (12674 * 112.578861248459) + 0.123756876809 := by gcongr
    _ ≤ (0.161417882536 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052777394883)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383307294) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282272016101) :
    parallelOracle 12674 0.011 xi bn cd ≤ 0.162410274070 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12674 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12674 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560502390082 : ℝ) ≤ plow 12674 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.578861248459 : ℝ) ≤ √(12674 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282272016101 : ℝ) / (2 * 0.560502390082 * 112.578861248459)) * 0.161417882536 +
        0.282272016101 ^ 2 / (2 * 0.560502390082 * 112.578861248459) := by gcongr
    _ ≤ (0.162410274070 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052777394883) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001383307294)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282272016101) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12674 12674 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560502390082 : ℝ) ≤ plow 12674 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.578861248459 : ℝ) ≤ √(12674 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12674 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12674 Θ 1.22 ≤ 0.011779302840 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.578861248459 := by gcongr <;> linarith
      _ ≤ (0.011779302840 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12674 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12674 12674 0.011 ≤ 0.008490821688 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12674 12674 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12674 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12674 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12674 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12674 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162410274070 + 0.011779302840 + (0.008490821688 : ℝ) *
        (1 + 2 * (0.282272016101 + 0.011779302840) / (0.560502390082 * 112.578861248459))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12674]

end BstLean.Part269.N12674

/-! The original eight local profiles supply actual 12674 moment certificates. -/
namespace BstLean.Part269.N12674
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12674 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12674 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12674 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052777394883 ∧
    0 ≤ bN 12674 BstLean.Part154.csC (groupTheta g) ∧ bN 12674 BstLean.Part154.csC (groupTheta g) ≤ 0.001383307294 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12674 12674 0.011
      (momentAllowance 12674 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12674 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12674 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12674 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12674 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12674 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229733312524 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12674 0.011
      (momentAllowance 12674 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12674 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12674
/-! The actual computed-centre upper energy formula at 12674. -/
namespace BstLean.Part269.N12674
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12674

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12674
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12674)
open BstLean.Part268 (cell12674)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085566449486
  | 2 => 0.086510607002
  | 3 => 0.087453110940
  | 4 => 0.088395426905
  | 5 => 0.089339326035
  | 6 => 0.090286930184
  | 7 => 0.091240761306
  | 8 => 0.092203795091
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12674 12674 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12674 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003543786177 + 0.003307136648 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S12.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S12.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12674

/-! Actual upper energy certificates on all 43 source endpoints at 12674. -/
namespace BstLean.Part269.N12674
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12674)
open BstLean.Part268 (cell12674)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12674 (gMinus 12674) (1 - (cell12674 i).lower) ≤ 1 ∧
    energyUpper 12674 (gMinus 12674) (BstLean.Part211.gPlus 12674)
      (finiteEnergy 12674 12674 0.011) (1 - (cell12674 i).lower) ≤
      (cell12674 i).energy := by
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
      have E := BstLean.Part269.S12.uniformEnergy10 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨10,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy11 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨11,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy12 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨12,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy13 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨13,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy14 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨14,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy15 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨15,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy16 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨16,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy17 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨17,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy18 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨18,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy19 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨19,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy20 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨20,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy21 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨21,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy22 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨22,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy23 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨23,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy24 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨24,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy25 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨25,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy26 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨26,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy27 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨27,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy28 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨28,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy29 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨29,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy30 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨30,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy31 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨31,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy32 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨32,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy33 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨33,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy34 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨34,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy35 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨35,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy36 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨36,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy37 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨37,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy38 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨38,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy39 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨39,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy40 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨40,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy41 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨41,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy42 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨42,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy43 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨43,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy44 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨44,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy45 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨45,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy46 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨46,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy47 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨47,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy48 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨48,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy49 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨49,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy50 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨50,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy51 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨51,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S12.uniformEnergy52 (n := 12674) (by norm_num)
        (q := 1 - (cell12674 ⟨52,by decide⟩).lower)
        (by norm_num [cell12674]) (by norm_num [cell12674])
      exact ⟨E.1,E.2.trans (by norm_num [cell12674])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12674

/-! Source-cell containment and simple scalar guards at 12674. -/
namespace BstLean.Part269.N12674
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12674)
open BstLean.Part268 (cell12674)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12674 ⟨10,by decide⟩).lower ∧ (cell12674 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12674 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12674 ⟨11,by decide⟩).lower ∧ (cell12674 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12674 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12674 ⟨12,by decide⟩).lower ∧ (cell12674 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12674 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12674 ⟨13,by decide⟩).lower ∧ (cell12674 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12674 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12674 ⟨14,by decide⟩).lower ∧ (cell12674 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12674 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12674 ⟨15,by decide⟩).lower ∧ (cell12674 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12674 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12674 ⟨16,by decide⟩).lower ∧ (cell12674 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12674 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12674 ⟨17,by decide⟩).lower ∧ (cell12674 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12674 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12674 ⟨18,by decide⟩).lower ∧ (cell12674 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12674 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12674 ⟨19,by decide⟩).lower ∧ (cell12674 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12674 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12674 ⟨20,by decide⟩).lower ∧ (cell12674 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12674 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12674 ⟨21,by decide⟩).lower ∧ (cell12674 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12674 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12674 ⟨22,by decide⟩).lower ∧ (cell12674 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12674 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12674 ⟨23,by decide⟩).lower ∧ (cell12674 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12674 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12674 ⟨24,by decide⟩).lower ∧ (cell12674 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12674 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12674 ⟨25,by decide⟩).lower ∧ (cell12674 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12674 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12674 ⟨26,by decide⟩).lower ∧ (cell12674 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12674 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12674 ⟨27,by decide⟩).lower ∧ (cell12674 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12674 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12674 ⟨28,by decide⟩).lower ∧ (cell12674 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12674 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12674 ⟨29,by decide⟩).lower ∧ (cell12674 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12674 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12674 ⟨30,by decide⟩).lower ∧ (cell12674 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12674 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12674 ⟨31,by decide⟩).lower ∧ (cell12674 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12674 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12674 ⟨32,by decide⟩).lower ∧ (cell12674 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12674 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12674 ⟨33,by decide⟩).lower ∧ (cell12674 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12674 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12674 ⟨34,by decide⟩).lower ∧ (cell12674 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12674 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12674 ⟨35,by decide⟩).lower ∧ (cell12674 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12674 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12674 ⟨36,by decide⟩).lower ∧ (cell12674 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12674 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12674 ⟨37,by decide⟩).lower ∧ (cell12674 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12674 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12674 ⟨38,by decide⟩).lower ∧ (cell12674 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12674 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12674 ⟨39,by decide⟩).lower ∧ (cell12674 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12674 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12674 ⟨40,by decide⟩).lower ∧ (cell12674 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12674 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12674 ⟨41,by decide⟩).lower ∧ (cell12674 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12674 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12674 ⟨42,by decide⟩).lower ∧ (cell12674 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12674 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12674 ⟨43,by decide⟩).lower ∧ (cell12674 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12674 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12674 ⟨44,by decide⟩).lower ∧ (cell12674 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12674 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12674 ⟨45,by decide⟩).lower ∧ (cell12674 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12674 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12674 ⟨46,by decide⟩).lower ∧ (cell12674 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12674 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12674 ⟨47,by decide⟩).lower ∧ (cell12674 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12674 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12674 ⟨48,by decide⟩).lower ∧ (cell12674 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12674 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12674 ⟨49,by decide⟩).lower ∧ (cell12674 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12674 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12674 ⟨50,by decide⟩).lower ∧ (cell12674 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12674 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12674 ⟨51,by decide⟩).lower ∧ (cell12674 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12674 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12674 ⟨52,by decide⟩).lower ∧ (cell12674 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12674 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12674 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12674 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12674,cell12674,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12674 i).lower ∧
    (cell12674 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12674 i).upper ≤ (0.532 : ℝ) ∧
    (cell12674 i).centre ≤ (0.1 : ℝ) ∧ (cell12674 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12674 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12674 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12674

/-! The local source numeric instances at 12674 have no network premises. -/
namespace BstLean.Part269.N12674
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12674)
open BstLean.Part268 (cell12674)

noncomputable def sourceNumerics12674 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12674 (cell12674 i)
      scalarRow12674.M scalarRow12674.H scalarRow12674.xi := by
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
    energy_allowance := scalarRow12674.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12674]
    centre_nonneg := (scalarRow12674.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D12.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12674])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12674