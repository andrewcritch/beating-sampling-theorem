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
import BstLean.Part269Direction20
import BstLean.Part269Shared20
import BstLean.Part269Finite
import BstLean.Part269Rows20
import BstLean.Part269Source
/-! Actual 12863 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12863
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12863 ≤ (1.035579621095 : ℝ) := by
  have hr : (113.415166534286 : ℝ) ≤ √(12863 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.415166534286 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12863 12863 (11 / 1000) ≤
    (0.008428211250 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12863) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.415166534286 : ℝ) ≤ √(12863 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12863)
  have hdiv : K / √(12863 : ℝ) ≤ K / 113.415166534286 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.415166534286 ≤ (0.008428211250 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12863.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12863 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12863 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12863 := gPlus_lower 12863
end BstLean.Part269.N12863

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12863
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035579621094 : ℝ) ≤ wn 12863 := by
  have hn : √(12863 : ℝ) ≤ 113.415166534287 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12863 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.415166534287 ≤ 2 / √(12863 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248633908 : ℝ) ≤ rhoBar 12863 BstLean.Part154.csC ∧
    rhoBar 12863 BstLean.Part154.csC ≤ 0.000248634293 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035579621094 : ℝ) / (1.295212 * 12863) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035579621095 : ℝ) / (1.29521 * 12863) := by gcongr
      _ ≤ (0.000248634293 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12863 BstLean.Part154.csC) ≤ 0.000994598992 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12863 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12863 BstLean.Part154.csC) (piBar (rhoBar 12863 BstLean.Part154.csC)) ≤ 0.000189908437 ∧
    cc1 (rhoBar 12863 BstLean.Part154.csC) (piBar (rhoBar 12863 BstLean.Part154.csC)) ≤ 0.000120840022 ∧
    cc2 (rhoBar 12863 BstLean.Part154.csC) ≤ 0.000070148587 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12863 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12863 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12863 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12863 BstLean.Part154.csC * nuR (rhoBar 12863 BstLean.Part154.csC)) ≤ 0.000497284041 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248634293 : ℝ) * 0.000994598992 := by gcongr
      _ ≤ (0.000497284041 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12863 BstLean.Part154.csC) * nuR (rhoBar 12863 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000994598992 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12863 BstLean.Part154.csC) * rhoBar 12863 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248634293 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248634293 / 2 + 0.399 * 0.000994598992 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189908437 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497284041 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120840022 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248634293 / 1.414213562 := by gcongr
      _ ≤ (0.000070148587 : ℝ) := by norm_num

end BstLean.Part269.N12863

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12863
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12863 BstLean.Part154.csC) (piBar (rhoBar 12863 BstLean.Part154.csC)) ≤ 1.55749E-7 := by
  have hr0 : 0 ≤ rhoBar 12863 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12863 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12863 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12863 BstLean.Part154.csC) (piBar (rhoBar 12863 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12863 BstLean.Part154.csC) (piBar (rhoBar 12863 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12863 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189908437 : ℝ) ^ 2 + 0.000120840022 ^ 2 + 3 * 0.000070148587 ^ 2 +
        2 * 0.797885 * 0.000189908437 * 0.000120840022 + 2 * 0.000189908437 * 0.000070148587 +
        4 * 0.797885 * 0.000120840022 * 0.000070148587 := by gcongr
    _ ≤ (1.55749E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12863 BstLean.Part154.csC Θ ≤ 0.002594826936 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12863 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12863 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12863 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12863 BstLean.Part154.csC) (piBar (rhoBar 12863 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12863 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035579621095 * 1.55749E-7 / (0.000248633908 : ℝ) := by gcongr
    _ ≤ 0.002594826936 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12863 BstLean.Part154.csC Θ ≤ 0.002878452164 + 0.000655669118 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12863 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12863 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12863 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035579621095 : ℝ) * ((2 * Θ * 0.000248634293 +
        (6863 / 10000) * 0.000248634293 * 12863 * 0.000994598992) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002878452164 + 0.000655669118 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12863 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12863 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12863 0.011 Θ ∧ gammaRatio 12863 0.011 Θ ≤ 0.000085474041 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12863 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035579621095 : ℝ) * 0.525 / ((1 - 0.011) * 12863) := by gcongr
      _ ≤ (0.000085474041 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12863 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12863 0.011 Θ) :=
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
    badAllowance 12863 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12863 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12863 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12863 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12863 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12863 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12863 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12863 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12863 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12863 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12863 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035579621095 : ℝ) * 12863 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12863 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003361195326 + 0.003250496054 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12863

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12863
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12863 BstLean.Part154.csC) (piBar (rhoBar 12863 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12863 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12863 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12863 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12863 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12863 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12863 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12863 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12863 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12863 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12863 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12863 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12863 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12863 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12863 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052147117445 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12863) ≤ 0.010529787308 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12863 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035579621095)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010529787308 + 2 * 0.737676 / 12863) := by gcongr
    _ ≤ (0.052147117445 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12863 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12863

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12863
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510846225 : ℝ) ≤ plow 12863 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12863) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052574305755)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362284142) : eMP 12863 0.011 xi bn ≤ 0.001173014111 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12863 : ℝ) * (1 - 0.011))) ≤ 0.000580015408 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001362284142 / (12863 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000580015408 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000580015408 : ℝ) + 3.141593 * 0.052574305755 / (12863 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001173014111 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052574305755)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362284142) : PiBarMP 12863 12 0.011 xi bn ≤ 0.160215804569 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12863 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036909133586 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.789658213862 : ℝ) ≤ √((12863 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.415166534286 : ℝ) ≤ √(12863 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12863) ≤ 0.122844313407 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036909133586 + 0.052574305755 * 1.772454 / (2 * (112.789658213862 : ℝ))) * (1 + 0.001173014111) +
        8 / (12863 * 113.415166534286) + 0.122844313407 := by gcongr
    _ ≤ (0.160215804569 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052574305755)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362284142) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281437993311) :
    parallelOracle 12863 0.011 xi bn cd ≤ 0.161193445878 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12863 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12863 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510846225 : ℝ) ≤ plow 12863 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.415166534286 : ℝ) ≤ √(12863 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281437993311 : ℝ) / (2 * 0.560510846225 * 113.415166534286)) * 0.160215804569 +
        0.281437993311 ^ 2 / (2 * 0.560510846225 * 113.415166534286) := by gcongr
    _ ≤ (0.161193445878 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052574305755) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362284142)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281437993311) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12863 12863 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510846225 : ℝ) ≤ plow 12863 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.415166534286 : ℝ) ≤ √(12863 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12863 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12863 Θ 1.22 ≤ 0.011692444146 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.415166534286 := by gcongr <;> linarith
      _ ≤ (0.011692444146 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12863 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12863 12863 0.011 ≤ 0.008428211250 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12863 12863 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12863 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12863 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12863 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12863 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161193445878 + 0.011692444146 + (0.008428211250 : ℝ) *
        (1 + 2 * (0.281437993311 + 0.011692444146) / (0.560510846225 * 113.415166534286))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12863]

end BstLean.Part269.N12863

/-! The original eight local profiles supply actual 12863 moment certificates. -/
namespace BstLean.Part269.N12863
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12863 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12863 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12863 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052574305755 ∧
    0 ≤ bN 12863 BstLean.Part154.csC (groupTheta g) ∧ bN 12863 BstLean.Part154.csC (groupTheta g) ≤ 0.001362284142 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12863 12863 0.011
      (momentAllowance 12863 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12863 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12863 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12863 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12863 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12863 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229290875866 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12863 0.011
      (momentAllowance 12863 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12863 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12863
/-! The actual computed-centre upper energy formula at 12863. -/
namespace BstLean.Part269.N12863
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12863

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12863
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12863)
open BstLean.Part268 (cell12863)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085028547281
  | 2 => 0.085963114812
  | 3 => 0.086894677642
  | 4 => 0.087824386896
  | 5 => 0.088753643169
  | 6 => 0.089684134625
  | 7 => 0.090617878882
  | 8 => 0.091557268745
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12863 12863 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12863 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12863

/-! Actual upper energy certificates on all 43 source endpoints at 12863. -/
namespace BstLean.Part269.N12863
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12863)
open BstLean.Part268 (cell12863)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12863 (gMinus 12863) (1 - (cell12863 i).lower) ≤ 1 ∧
    energyUpper 12863 (gMinus 12863) (BstLean.Part211.gPlus 12863)
      (finiteEnergy 12863 12863 0.011) (1 - (cell12863 i).lower) ≤
      (cell12863 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨10,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨11,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨12,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨13,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨14,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨15,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨16,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨17,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨18,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨19,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨20,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨21,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨22,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨23,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨24,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨25,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨26,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨27,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨28,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨29,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨30,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨31,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨32,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨33,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨34,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨35,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨36,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨37,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨38,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨39,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨40,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨41,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨42,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨43,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨44,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨45,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨46,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨47,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨48,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨49,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨50,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨51,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12863) (by norm_num)
        (q := 1 - (cell12863 ⟨52,by decide⟩).lower)
        (by norm_num [cell12863]) (by norm_num [cell12863])
      exact ⟨E.1,E.2.trans (by norm_num [cell12863])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12863

/-! Source-cell containment and simple scalar guards at 12863. -/
namespace BstLean.Part269.N12863
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12863)
open BstLean.Part268 (cell12863)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12863 ⟨10,by decide⟩).lower ∧ (cell12863 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12863 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12863 ⟨11,by decide⟩).lower ∧ (cell12863 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12863 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12863 ⟨12,by decide⟩).lower ∧ (cell12863 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12863 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12863 ⟨13,by decide⟩).lower ∧ (cell12863 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12863 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12863 ⟨14,by decide⟩).lower ∧ (cell12863 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12863 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12863 ⟨15,by decide⟩).lower ∧ (cell12863 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12863 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12863 ⟨16,by decide⟩).lower ∧ (cell12863 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12863 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12863 ⟨17,by decide⟩).lower ∧ (cell12863 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12863 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12863 ⟨18,by decide⟩).lower ∧ (cell12863 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12863 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12863 ⟨19,by decide⟩).lower ∧ (cell12863 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12863 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12863 ⟨20,by decide⟩).lower ∧ (cell12863 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12863 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12863 ⟨21,by decide⟩).lower ∧ (cell12863 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12863 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12863 ⟨22,by decide⟩).lower ∧ (cell12863 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12863 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12863 ⟨23,by decide⟩).lower ∧ (cell12863 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12863 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12863 ⟨24,by decide⟩).lower ∧ (cell12863 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12863 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12863 ⟨25,by decide⟩).lower ∧ (cell12863 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12863 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12863 ⟨26,by decide⟩).lower ∧ (cell12863 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12863 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12863 ⟨27,by decide⟩).lower ∧ (cell12863 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12863 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12863 ⟨28,by decide⟩).lower ∧ (cell12863 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12863 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12863 ⟨29,by decide⟩).lower ∧ (cell12863 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12863 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12863 ⟨30,by decide⟩).lower ∧ (cell12863 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12863 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12863 ⟨31,by decide⟩).lower ∧ (cell12863 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12863 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12863 ⟨32,by decide⟩).lower ∧ (cell12863 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12863 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12863 ⟨33,by decide⟩).lower ∧ (cell12863 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12863 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12863 ⟨34,by decide⟩).lower ∧ (cell12863 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12863 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12863 ⟨35,by decide⟩).lower ∧ (cell12863 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12863 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12863 ⟨36,by decide⟩).lower ∧ (cell12863 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12863 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12863 ⟨37,by decide⟩).lower ∧ (cell12863 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12863 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12863 ⟨38,by decide⟩).lower ∧ (cell12863 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12863 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12863 ⟨39,by decide⟩).lower ∧ (cell12863 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12863 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12863 ⟨40,by decide⟩).lower ∧ (cell12863 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12863 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12863 ⟨41,by decide⟩).lower ∧ (cell12863 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12863 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12863 ⟨42,by decide⟩).lower ∧ (cell12863 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12863 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12863 ⟨43,by decide⟩).lower ∧ (cell12863 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12863 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12863 ⟨44,by decide⟩).lower ∧ (cell12863 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12863 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12863 ⟨45,by decide⟩).lower ∧ (cell12863 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12863 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12863 ⟨46,by decide⟩).lower ∧ (cell12863 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12863 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12863 ⟨47,by decide⟩).lower ∧ (cell12863 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12863 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12863 ⟨48,by decide⟩).lower ∧ (cell12863 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12863 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12863 ⟨49,by decide⟩).lower ∧ (cell12863 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12863 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12863 ⟨50,by decide⟩).lower ∧ (cell12863 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12863 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12863 ⟨51,by decide⟩).lower ∧ (cell12863 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12863 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12863 ⟨52,by decide⟩).lower ∧ (cell12863 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12863 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12863 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12863 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12863,cell12863,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12863 i).lower ∧
    (cell12863 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12863 i).upper ≤ (0.532 : ℝ) ∧
    (cell12863 i).centre ≤ (0.1 : ℝ) ∧ (cell12863 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12863 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12863 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12863

/-! The local source numeric instances at 12863 have no network premises. -/
namespace BstLean.Part269.N12863
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12863)
open BstLean.Part268 (cell12863)

noncomputable def sourceNumerics12863 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12863 (cell12863 i)
      scalarRow12863.M scalarRow12863.H scalarRow12863.xi := by
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
    energy_allowance := scalarRow12863.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12863]
    centre_nonneg := (scalarRow12863.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12863])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12863
/-! Actual 12864 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12864
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12864 ≤ (1.035578226067 : ℝ) := by
  have hr : (113.419575030062 : ℝ) ≤ √(12864 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.419575030062 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12864 12864 (11 / 1000) ≤
    (0.008427883653 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12864) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.419575030062 : ℝ) ≤ √(12864 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12864)
  have hdiv : K / √(12864 : ℝ) ≤ K / 113.419575030062 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.419575030062 ≤ (0.008427883653 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12864.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12864 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12864 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12864 := gPlus_lower 12864
end BstLean.Part269.N12864

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12864
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035578226066 : ℝ) ≤ wn 12864 := by
  have hn : √(12864 : ℝ) ≤ 113.419575030063 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12864 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.419575030063 ≤ 2 / √(12864 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248614246 : ℝ) ≤ rhoBar 12864 BstLean.Part154.csC ∧
    rhoBar 12864 BstLean.Part154.csC ≤ 0.000248614630 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035578226066 : ℝ) / (1.295212 * 12864) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035578226067 : ℝ) / (1.29521 * 12864) := by gcongr
      _ ≤ (0.000248614630 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12864 BstLean.Part154.csC) ≤ 0.000994520330 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12864 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12864 BstLean.Part154.csC) (piBar (rhoBar 12864 BstLean.Part154.csC)) ≤ 0.000189893417 ∧
    cc1 (rhoBar 12864 BstLean.Part154.csC) (piBar (rhoBar 12864 BstLean.Part154.csC)) ≤ 0.000120830466 ∧
    cc2 (rhoBar 12864 BstLean.Part154.csC) ≤ 0.000070143040 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12864 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12864 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12864 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12864 BstLean.Part154.csC * nuR (rhoBar 12864 BstLean.Part154.csC)) ≤ 0.000497244713 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248614630 : ℝ) * 0.000994520330 := by gcongr
      _ ≤ (0.000497244713 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12864 BstLean.Part154.csC) * nuR (rhoBar 12864 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000994520330 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12864 BstLean.Part154.csC) * rhoBar 12864 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248614630 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248614630 / 2 + 0.399 * 0.000994520330 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189893417 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497244713 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120830466 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248614630 / 1.414213562 := by gcongr
      _ ≤ (0.000070143040 : ℝ) := by norm_num

end BstLean.Part269.N12864

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12864
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12864 BstLean.Part154.csC) (piBar (rhoBar 12864 BstLean.Part154.csC)) ≤ 1.55724E-7 := by
  have hr0 : 0 ≤ rhoBar 12864 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12864 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12864 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12864 BstLean.Part154.csC) (piBar (rhoBar 12864 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12864 BstLean.Part154.csC) (piBar (rhoBar 12864 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12864 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189893417 : ℝ) ^ 2 + 0.000120830466 ^ 2 + 3 * 0.000070143040 ^ 2 +
        2 * 0.797885 * 0.000189893417 * 0.000120830466 + 2 * 0.000189893417 * 0.000070143040 +
        4 * 0.797885 * 0.000120830466 * 0.000070143040 := by gcongr
    _ ≤ (1.55724E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12864 BstLean.Part154.csC Θ ≤ 0.002594612116 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12864 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12864 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12864 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12864 BstLean.Part154.csC) (piBar (rhoBar 12864 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12864 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035578226067 * 1.55724E-7 / (0.000248614246 : ℝ) := by gcongr
    _ ≤ 0.002594612116 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12864 BstLean.Part154.csC Θ ≤ 0.002878216753 + 0.000655616382 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12864 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12864 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12864 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035578226067 : ℝ) * ((2 * Θ * 0.000248614630 +
        (6863 / 10000) * 0.000248614630 * 12864 * 0.000994520330) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002878216753 + 0.000655616382 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12864 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12864 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12864 0.011 Θ ∧ gammaRatio 12864 0.011 Θ ≤ 0.000085467281 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12864 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035578226067 : ℝ) * 0.525 / ((1 - 0.011) * 12864) := by gcongr
      _ ≤ (0.000085467281 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12864 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12864 0.011 Θ) :=
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
    badAllowance 12864 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12864 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12864 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12864 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12864 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12864 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12864 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12864 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12864 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12864 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12864 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035578226067 : ℝ) * 12864 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12864 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003360959915 + 0.003250228498 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12864

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12864
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12864 BstLean.Part154.csC) (piBar (rhoBar 12864 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12864 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12864 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12864 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12864 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12864 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12864 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12864 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12864 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12864 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12864 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12864 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12864 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12864 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12864 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052145068706 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12864) ≤ 0.010529378027 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12864 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035578226067)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010529378027 + 2 * 0.737676 / 12864) := by gcongr
    _ ≤ (0.052145068706 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12864 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12864

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12864
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510890306 : ℝ) ≤ plow 12864 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12864) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052573929877)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362171361) : eMP 12864 0.011 xi bn ≤ 0.001172919903 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12864 : ℝ) * (1 - 0.011))) ≤ 0.000579968855 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001362171361 / (12864 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579968855 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579968855 : ℝ) + 3.141593 * 0.052573929877 / (12864 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001172919903 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052573929877)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362171361) : PiBarMP 12864 12 0.011 xi bn ≤ 0.160209476912 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12864 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036907605734 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.794042395864 : ℝ) ≤ √((12864 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.419575030062 : ℝ) ≤ √(12864 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12864) ≤ 0.122839538582 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036907605734 + 0.052573929877 * 1.772454 / (2 * (112.794042395864 : ℝ))) * (1 + 0.001172919903) +
        8 / (12864 * 113.419575030062) + 0.122839538582 := by gcongr
    _ ≤ (0.160209476912 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052573929877)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362171361) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281435124917) :
    parallelOracle 12864 0.011 xi bn cd ≤ 0.161187049825 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12864 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12864 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510890306 : ℝ) ≤ plow 12864 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.419575030062 : ℝ) ≤ √(12864 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281435124917 : ℝ) / (2 * 0.560510890306 * 113.419575030062)) * 0.160209476912 +
        0.281435124917 ^ 2 / (2 * 0.560510890306 * 113.419575030062) := by gcongr
    _ ≤ (0.161187049825 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052573929877) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362171361)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281435124917) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12864 12864 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510890306 : ℝ) ≤ plow 12864 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.419575030062 : ℝ) ≤ √(12864 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12864 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12864 Θ 1.22 ≤ 0.011691989674 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.419575030062 := by gcongr <;> linarith
      _ ≤ (0.011691989674 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12864 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12864 12864 0.011 ≤ 0.008427883653 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12864 12864 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12864 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12864 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12864 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12864 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161187049825 + 0.011691989674 + (0.008427883653 : ℝ) *
        (1 + 2 * (0.281435124917 + 0.011691989674) / (0.560510890306 * 113.419575030062))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12864]

end BstLean.Part269.N12864

/-! The original eight local profiles supply actual 12864 moment certificates. -/
namespace BstLean.Part269.N12864
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12864 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12864 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12864 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052573929877 ∧
    0 ≤ bN 12864 BstLean.Part154.csC (groupTheta g) ∧ bN 12864 BstLean.Part154.csC (groupTheta g) ≤ 0.001362171361 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12864 12864 0.011
      (momentAllowance 12864 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12864 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12864 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12864 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12864 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12864 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229290056211 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12864 0.011
      (momentAllowance 12864 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12864 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12864
/-! The actual computed-centre upper energy formula at 12864. -/
namespace BstLean.Part269.N12864
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12864

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12864
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12864)
open BstLean.Part268 (cell12864)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085025794514
  | 2 => 0.085960315023
  | 3 => 0.086891824557
  | 4 => 0.087821472757
  | 5 => 0.088750658466
  | 6 => 0.089681067794
  | 7 => 0.090614715962
  | 8 => 0.091553993001
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12864 12864 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12864 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12864

/-! Actual upper energy certificates on all 43 source endpoints at 12864. -/
namespace BstLean.Part269.N12864
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12864)
open BstLean.Part268 (cell12864)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12864 (gMinus 12864) (1 - (cell12864 i).lower) ≤ 1 ∧
    energyUpper 12864 (gMinus 12864) (BstLean.Part211.gPlus 12864)
      (finiteEnergy 12864 12864 0.011) (1 - (cell12864 i).lower) ≤
      (cell12864 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨10,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨11,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨12,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨13,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨14,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨15,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨16,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨17,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨18,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨19,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨20,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨21,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨22,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨23,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨24,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨25,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨26,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨27,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨28,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨29,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨30,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨31,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨32,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨33,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨34,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨35,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨36,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨37,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨38,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨39,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨40,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨41,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨42,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨43,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨44,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨45,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨46,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨47,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨48,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨49,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨50,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨51,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12864) (by norm_num)
        (q := 1 - (cell12864 ⟨52,by decide⟩).lower)
        (by norm_num [cell12864]) (by norm_num [cell12864])
      exact ⟨E.1,E.2.trans (by norm_num [cell12864])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12864

/-! Source-cell containment and simple scalar guards at 12864. -/
namespace BstLean.Part269.N12864
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12864)
open BstLean.Part268 (cell12864)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12864 ⟨10,by decide⟩).lower ∧ (cell12864 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12864 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12864 ⟨11,by decide⟩).lower ∧ (cell12864 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12864 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12864 ⟨12,by decide⟩).lower ∧ (cell12864 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12864 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12864 ⟨13,by decide⟩).lower ∧ (cell12864 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12864 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12864 ⟨14,by decide⟩).lower ∧ (cell12864 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12864 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12864 ⟨15,by decide⟩).lower ∧ (cell12864 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12864 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12864 ⟨16,by decide⟩).lower ∧ (cell12864 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12864 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12864 ⟨17,by decide⟩).lower ∧ (cell12864 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12864 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12864 ⟨18,by decide⟩).lower ∧ (cell12864 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12864 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12864 ⟨19,by decide⟩).lower ∧ (cell12864 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12864 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12864 ⟨20,by decide⟩).lower ∧ (cell12864 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12864 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12864 ⟨21,by decide⟩).lower ∧ (cell12864 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12864 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12864 ⟨22,by decide⟩).lower ∧ (cell12864 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12864 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12864 ⟨23,by decide⟩).lower ∧ (cell12864 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12864 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12864 ⟨24,by decide⟩).lower ∧ (cell12864 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12864 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12864 ⟨25,by decide⟩).lower ∧ (cell12864 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12864 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12864 ⟨26,by decide⟩).lower ∧ (cell12864 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12864 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12864 ⟨27,by decide⟩).lower ∧ (cell12864 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12864 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12864 ⟨28,by decide⟩).lower ∧ (cell12864 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12864 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12864 ⟨29,by decide⟩).lower ∧ (cell12864 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12864 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12864 ⟨30,by decide⟩).lower ∧ (cell12864 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12864 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12864 ⟨31,by decide⟩).lower ∧ (cell12864 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12864 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12864 ⟨32,by decide⟩).lower ∧ (cell12864 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12864 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12864 ⟨33,by decide⟩).lower ∧ (cell12864 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12864 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12864 ⟨34,by decide⟩).lower ∧ (cell12864 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12864 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12864 ⟨35,by decide⟩).lower ∧ (cell12864 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12864 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12864 ⟨36,by decide⟩).lower ∧ (cell12864 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12864 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12864 ⟨37,by decide⟩).lower ∧ (cell12864 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12864 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12864 ⟨38,by decide⟩).lower ∧ (cell12864 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12864 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12864 ⟨39,by decide⟩).lower ∧ (cell12864 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12864 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12864 ⟨40,by decide⟩).lower ∧ (cell12864 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12864 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12864 ⟨41,by decide⟩).lower ∧ (cell12864 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12864 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12864 ⟨42,by decide⟩).lower ∧ (cell12864 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12864 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12864 ⟨43,by decide⟩).lower ∧ (cell12864 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12864 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12864 ⟨44,by decide⟩).lower ∧ (cell12864 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12864 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12864 ⟨45,by decide⟩).lower ∧ (cell12864 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12864 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12864 ⟨46,by decide⟩).lower ∧ (cell12864 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12864 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12864 ⟨47,by decide⟩).lower ∧ (cell12864 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12864 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12864 ⟨48,by decide⟩).lower ∧ (cell12864 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12864 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12864 ⟨49,by decide⟩).lower ∧ (cell12864 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12864 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12864 ⟨50,by decide⟩).lower ∧ (cell12864 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12864 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12864 ⟨51,by decide⟩).lower ∧ (cell12864 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12864 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12864 ⟨52,by decide⟩).lower ∧ (cell12864 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12864 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12864 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12864 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12864,cell12864,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12864 i).lower ∧
    (cell12864 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12864 i).upper ≤ (0.532 : ℝ) ∧
    (cell12864 i).centre ≤ (0.1 : ℝ) ∧ (cell12864 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12864 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12864 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12864

/-! The local source numeric instances at 12864 have no network premises. -/
namespace BstLean.Part269.N12864
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12864)
open BstLean.Part268 (cell12864)

noncomputable def sourceNumerics12864 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12864 (cell12864 i)
      scalarRow12864.M scalarRow12864.H scalarRow12864.xi := by
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
    energy_allowance := scalarRow12864.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12864]
    centre_nonneg := (scalarRow12864.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12864])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12864
/-! Actual 12865 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12865
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12865 ≤ (1.035576831203 : ℝ) := by
  have hr : (113.423983354491 : ℝ) ≤ √(12865 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.423983354491 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12865 12865 (11 / 1000) ≤
    (0.008427556093 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12865) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.423983354491 : ℝ) ≤ √(12865 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12865)
  have hdiv : K / √(12865 : ℝ) ≤ K / 113.423983354491 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.423983354491 ≤ (0.008427556093 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12865.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12865 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12865 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12865 := gPlus_lower 12865
end BstLean.Part269.N12865

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12865
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035576831202 : ℝ) ≤ wn 12865 := by
  have hn : √(12865 : ℝ) ≤ 113.423983354492 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12865 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.423983354492 ≤ 2 / √(12865 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248594586 : ℝ) ≤ rhoBar 12865 BstLean.Part154.csC ∧
    rhoBar 12865 BstLean.Part154.csC ≤ 0.000248594971 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035576831202 : ℝ) / (1.295212 * 12865) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035576831203 : ℝ) / (1.29521 * 12865) := by gcongr
      _ ≤ (0.000248594971 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12865 BstLean.Part154.csC) ≤ 0.000994441684 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12865 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12865 BstLean.Part154.csC) (piBar (rhoBar 12865 BstLean.Part154.csC)) ≤ 0.000189878401 ∧
    cc1 (rhoBar 12865 BstLean.Part154.csC) (piBar (rhoBar 12865 BstLean.Part154.csC)) ≤ 0.000120820911 ∧
    cc2 (rhoBar 12865 BstLean.Part154.csC) ≤ 0.000070137493 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12865 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12865 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12865 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12865 BstLean.Part154.csC * nuR (rhoBar 12865 BstLean.Part154.csC)) ≤ 0.000497205392 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248594971 : ℝ) * 0.000994441684 := by gcongr
      _ ≤ (0.000497205392 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12865 BstLean.Part154.csC) * nuR (rhoBar 12865 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000994441684 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12865 BstLean.Part154.csC) * rhoBar 12865 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248594971 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248594971 / 2 + 0.399 * 0.000994441684 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189878401 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497205392 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120820911 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248594971 / 1.414213562 := by gcongr
      _ ≤ (0.000070137493 : ℝ) := by norm_num

end BstLean.Part269.N12865

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12865
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12865 BstLean.Part154.csC) (piBar (rhoBar 12865 BstLean.Part154.csC)) ≤ 1.55699E-7 := by
  have hr0 : 0 ≤ rhoBar 12865 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12865 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12865 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12865 BstLean.Part154.csC) (piBar (rhoBar 12865 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12865 BstLean.Part154.csC) (piBar (rhoBar 12865 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12865 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189878401 : ℝ) ^ 2 + 0.000120820911 ^ 2 + 3 * 0.000070137493 ^ 2 +
        2 * 0.797885 * 0.000189878401 * 0.000120820911 + 2 * 0.000189878401 * 0.000070137493 +
        4 * 0.797885 * 0.000120820911 * 0.000070137493 := by gcongr
    _ ≤ (1.55699E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12865 BstLean.Part154.csC Θ ≤ 0.002594397242 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12865 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12865 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12865 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12865 BstLean.Part154.csC) (piBar (rhoBar 12865 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12865 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035576831203 * 1.55699E-7 / (0.000248594586 : ℝ) := by gcongr
    _ ≤ 0.002594397242 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12865 BstLean.Part154.csC Θ ≤ 0.002877981402 + 0.000655563657 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12865 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12865 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12865 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035576831203 : ℝ) * ((2 * Θ * 0.000248594971 +
        (6863 / 10000) * 0.000248594971 * 12865 * 0.000994441684) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002877981402 + 0.000655563657 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12865 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12865 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12865 0.011 Θ ∧ gammaRatio 12865 0.011 Θ ≤ 0.000085460523 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12865 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035576831203 : ℝ) * 0.525 / ((1 - 0.011) * 12865) := by gcongr
      _ ≤ (0.000085460523 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12865 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12865 0.011 Θ) :=
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
    badAllowance 12865 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12865 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12865 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12865 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12865 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12865 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12865 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12865 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12865 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12865 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12865 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035576831203 : ℝ) * 12865 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12865 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003360724564 + 0.003249960899 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12865

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12865
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12865 BstLean.Part154.csC) (piBar (rhoBar 12865 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12865 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12865 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12865 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12865 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12865 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12865 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12865 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12865 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12865 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12865 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12865 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12865 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12865 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12865 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052143020203 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12865) ≤ 0.010528968793 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12865 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035576831203)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010528968793 + 2 * 0.737676 / 12865) := by gcongr
    _ ≤ (0.052143020203 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12865 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12865

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12865
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510934380 : ℝ) ≤ plow 12865 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12865) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052573554036)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362058553) : eMP 12865 0.011 xi bn ≤ 0.001172825689 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12865 : ℝ) * (1 - 0.011))) ≤ 0.000579922299 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001362058553 / (12865 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579922299 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579922299 : ℝ) + 3.141593 * 0.052573554036 / (12865 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001172825689 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052573554036)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362058553) : PiBarMP 12865 12 0.011 xi bn ≤ 0.160203149386 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12865 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036906077454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.798426407463 : ℝ) ≤ √((12865 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.423983354491 : ℝ) ≤ √(12865 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12865) ≤ 0.122834764313 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036906077454 + 0.052573554036 * 1.772454 / (2 * (112.798426407463 : ℝ))) * (1 + 0.001172825689) +
        8 / (12865 * 113.423983354491) + 0.122834764313 := by gcongr
    _ ≤ (0.160203149386 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052573554036)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362058553) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281432256837) :
    parallelOracle 12865 0.011 xi bn cd ≤ 0.161180653913 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12865 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12865 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510934380 : ℝ) ≤ plow 12865 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.423983354491 : ℝ) ≤ √(12865 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281432256837 : ℝ) / (2 * 0.560510934380 * 113.423983354491)) * 0.160203149386 +
        0.281432256837 ^ 2 / (2 * 0.560510934380 * 113.423983354491) := by gcongr
    _ ≤ (0.161180653913 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052573554036) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001362058553)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281432256837) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12865 12865 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510934380 : ℝ) ≤ plow 12865 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.423983354491 : ℝ) ≤ √(12865 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12865 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12865 Θ 1.22 ≤ 0.011691535254 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.423983354491 := by gcongr <;> linarith
      _ ≤ (0.011691535254 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12865 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12865 12865 0.011 ≤ 0.008427556093 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12865 12865 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12865 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12865 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12865 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12865 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161180653913 + 0.011691535254 + (0.008427556093 : ℝ) *
        (1 + 2 * (0.281432256837 + 0.011691535254) / (0.560510934380 * 113.423983354491))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12865]

end BstLean.Part269.N12865

/-! The original eight local profiles supply actual 12865 moment certificates. -/
namespace BstLean.Part269.N12865
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12865 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12865 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12865 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052573554036 ∧
    0 ≤ bN 12865 BstLean.Part154.csC (groupTheta g) ∧ bN 12865 BstLean.Part154.csC (groupTheta g) ≤ 0.001362058553 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12865 12865 0.011
      (momentAllowance 12865 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12865 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12865 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12865 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12865 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12865 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229289236634 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12865 0.011
      (momentAllowance 12865 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12865 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12865
/-! The actual computed-centre upper energy formula at 12865. -/
namespace BstLean.Part269.N12865
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12865

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12865
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12865)
open BstLean.Part268 (cell12865)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085023042669
  | 2 => 0.085957516192
  | 3 => 0.086888972474
  | 4 => 0.087818559675
  | 5 => 0.088747674888
  | 6 => 0.089678002169
  | 7 => 0.090611554346
  | 8 => 0.091550718680
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12865 12865 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12865 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12865

/-! Actual upper energy certificates on all 43 source endpoints at 12865. -/
namespace BstLean.Part269.N12865
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12865)
open BstLean.Part268 (cell12865)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12865 (gMinus 12865) (1 - (cell12865 i).lower) ≤ 1 ∧
    energyUpper 12865 (gMinus 12865) (BstLean.Part211.gPlus 12865)
      (finiteEnergy 12865 12865 0.011) (1 - (cell12865 i).lower) ≤
      (cell12865 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨10,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨11,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨12,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨13,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨14,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨15,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨16,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨17,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨18,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨19,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨20,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨21,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨22,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨23,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨24,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨25,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨26,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨27,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨28,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨29,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨30,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨31,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨32,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨33,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨34,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨35,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨36,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨37,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨38,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨39,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨40,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨41,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨42,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨43,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨44,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨45,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨46,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨47,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨48,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨49,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨50,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨51,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12865) (by norm_num)
        (q := 1 - (cell12865 ⟨52,by decide⟩).lower)
        (by norm_num [cell12865]) (by norm_num [cell12865])
      exact ⟨E.1,E.2.trans (by norm_num [cell12865])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12865

/-! Source-cell containment and simple scalar guards at 12865. -/
namespace BstLean.Part269.N12865
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12865)
open BstLean.Part268 (cell12865)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12865 ⟨10,by decide⟩).lower ∧ (cell12865 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12865 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12865 ⟨11,by decide⟩).lower ∧ (cell12865 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12865 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12865 ⟨12,by decide⟩).lower ∧ (cell12865 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12865 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12865 ⟨13,by decide⟩).lower ∧ (cell12865 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12865 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12865 ⟨14,by decide⟩).lower ∧ (cell12865 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12865 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12865 ⟨15,by decide⟩).lower ∧ (cell12865 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12865 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12865 ⟨16,by decide⟩).lower ∧ (cell12865 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12865 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12865 ⟨17,by decide⟩).lower ∧ (cell12865 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12865 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12865 ⟨18,by decide⟩).lower ∧ (cell12865 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12865 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12865 ⟨19,by decide⟩).lower ∧ (cell12865 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12865 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12865 ⟨20,by decide⟩).lower ∧ (cell12865 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12865 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12865 ⟨21,by decide⟩).lower ∧ (cell12865 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12865 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12865 ⟨22,by decide⟩).lower ∧ (cell12865 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12865 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12865 ⟨23,by decide⟩).lower ∧ (cell12865 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12865 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12865 ⟨24,by decide⟩).lower ∧ (cell12865 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12865 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12865 ⟨25,by decide⟩).lower ∧ (cell12865 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12865 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12865 ⟨26,by decide⟩).lower ∧ (cell12865 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12865 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12865 ⟨27,by decide⟩).lower ∧ (cell12865 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12865 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12865 ⟨28,by decide⟩).lower ∧ (cell12865 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12865 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12865 ⟨29,by decide⟩).lower ∧ (cell12865 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12865 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12865 ⟨30,by decide⟩).lower ∧ (cell12865 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12865 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12865 ⟨31,by decide⟩).lower ∧ (cell12865 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12865 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12865 ⟨32,by decide⟩).lower ∧ (cell12865 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12865 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12865 ⟨33,by decide⟩).lower ∧ (cell12865 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12865 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12865 ⟨34,by decide⟩).lower ∧ (cell12865 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12865 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12865 ⟨35,by decide⟩).lower ∧ (cell12865 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12865 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12865 ⟨36,by decide⟩).lower ∧ (cell12865 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12865 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12865 ⟨37,by decide⟩).lower ∧ (cell12865 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12865 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12865 ⟨38,by decide⟩).lower ∧ (cell12865 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12865 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12865 ⟨39,by decide⟩).lower ∧ (cell12865 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12865 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12865 ⟨40,by decide⟩).lower ∧ (cell12865 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12865 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12865 ⟨41,by decide⟩).lower ∧ (cell12865 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12865 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12865 ⟨42,by decide⟩).lower ∧ (cell12865 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12865 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12865 ⟨43,by decide⟩).lower ∧ (cell12865 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12865 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12865 ⟨44,by decide⟩).lower ∧ (cell12865 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12865 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12865 ⟨45,by decide⟩).lower ∧ (cell12865 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12865 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12865 ⟨46,by decide⟩).lower ∧ (cell12865 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12865 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12865 ⟨47,by decide⟩).lower ∧ (cell12865 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12865 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12865 ⟨48,by decide⟩).lower ∧ (cell12865 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12865 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12865 ⟨49,by decide⟩).lower ∧ (cell12865 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12865 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12865 ⟨50,by decide⟩).lower ∧ (cell12865 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12865 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12865 ⟨51,by decide⟩).lower ∧ (cell12865 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12865 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12865 ⟨52,by decide⟩).lower ∧ (cell12865 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12865 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12865 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12865 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12865,cell12865,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12865 i).lower ∧
    (cell12865 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12865 i).upper ≤ (0.532 : ℝ) ∧
    (cell12865 i).centre ≤ (0.1 : ℝ) ∧ (cell12865 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12865 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12865 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12865

/-! The local source numeric instances at 12865 have no network premises. -/
namespace BstLean.Part269.N12865
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12865)
open BstLean.Part268 (cell12865)

noncomputable def sourceNumerics12865 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12865 (cell12865 i)
      scalarRow12865.M scalarRow12865.H scalarRow12865.xi := by
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
    energy_allowance := scalarRow12865.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12865]
    centre_nonneg := (scalarRow12865.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12865])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12865
/-! Actual 12866 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12866
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12866 ≤ (1.035575436502 : ℝ) := by
  have hr : (113.428391507593 : ℝ) ≤ √(12866 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.428391507593 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12866 12866 (11 / 1000) ≤
    (0.008427228571 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12866) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.428391507593 : ℝ) ≤ √(12866 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12866)
  have hdiv : K / √(12866 : ℝ) ≤ K / 113.428391507593 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.428391507593 ≤ (0.008427228571 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12866.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12866 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12866 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12866 := gPlus_lower 12866
end BstLean.Part269.N12866

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12866
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035575436501 : ℝ) ≤ wn 12866 := by
  have hn : √(12866 : ℝ) ≤ 113.428391507594 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12866 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.428391507594 ≤ 2 / √(12866 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248574929 : ℝ) ≤ rhoBar 12866 BstLean.Part154.csC ∧
    rhoBar 12866 BstLean.Part154.csC ≤ 0.000248575314 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035575436501 : ℝ) / (1.295212 * 12866) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035575436502 : ℝ) / (1.29521 * 12866) := by gcongr
      _ ≤ (0.000248575314 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12866 BstLean.Part154.csC) ≤ 0.000994363046 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12866 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12866 BstLean.Part154.csC) (piBar (rhoBar 12866 BstLean.Part154.csC)) ≤ 0.000189863386 ∧
    cc1 (rhoBar 12866 BstLean.Part154.csC) (piBar (rhoBar 12866 BstLean.Part154.csC)) ≤ 0.000120811357 ∧
    cc2 (rhoBar 12866 BstLean.Part154.csC) ≤ 0.000070131947 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12866 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12866 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12866 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12866 BstLean.Part154.csC * nuR (rhoBar 12866 BstLean.Part154.csC)) ≤ 0.000497166076 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248575314 : ℝ) * 0.000994363046 := by gcongr
      _ ≤ (0.000497166076 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12866 BstLean.Part154.csC) * nuR (rhoBar 12866 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000994363046 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12866 BstLean.Part154.csC) * rhoBar 12866 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248575314 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248575314 / 2 + 0.399 * 0.000994363046 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189863386 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497166076 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120811357 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248575314 / 1.414213562 := by gcongr
      _ ≤ (0.000070131947 : ℝ) := by norm_num

end BstLean.Part269.N12866

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12866
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12866 BstLean.Part154.csC) (piBar (rhoBar 12866 BstLean.Part154.csC)) ≤ 1.55675E-7 := by
  have hr0 : 0 ≤ rhoBar 12866 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12866 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12866 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12866 BstLean.Part154.csC) (piBar (rhoBar 12866 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12866 BstLean.Part154.csC) (piBar (rhoBar 12866 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12866 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189863386 : ℝ) ^ 2 + 0.000120811357 ^ 2 + 3 * 0.000070131947 ^ 2 +
        2 * 0.797885 * 0.000189863386 * 0.000120811357 + 2 * 0.000189863386 * 0.000070131947 +
        4 * 0.797885 * 0.000120811357 * 0.000070131947 := by gcongr
    _ ≤ (1.55675E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12866 BstLean.Part154.csC Θ ≤ 0.002594198969 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12866 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12866 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12866 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12866 BstLean.Part154.csC) (piBar (rhoBar 12866 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12866 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035575436502 * 1.55675E-7 / (0.000248574929 : ℝ) := by gcongr
    _ ≤ 0.002594198969 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12866 BstLean.Part154.csC Θ ≤ 0.002877746062 + 0.000655510937 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12866 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12866 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12866 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035575436502 : ℝ) * ((2 * Θ * 0.000248575314 +
        (6863 / 10000) * 0.000248575314 * 12866 * 0.000994363046) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002877746062 + 0.000655510937 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12866 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12866 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12866 0.011 Θ ∧ gammaRatio 12866 0.011 Θ ≤ 0.000085453765 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12866 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035575436502 : ℝ) * 0.525 / ((1 - 0.011) * 12866) := by gcongr
      _ ≤ (0.000085453765 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12866 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12866 0.011 Θ) :=
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
    badAllowance 12866 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12866 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12866 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12866 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12866 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12866 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12866 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12866 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12866 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12866 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12866 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035575436502 : ℝ) * 12866 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12866 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003360489224 + 0.003249709906 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12866

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12866
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12866 BstLean.Part154.csC) (piBar (rhoBar 12866 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12866 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12866 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12866 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12866 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12866 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12866 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12866 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12866 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12866 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12866 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12866 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12866 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12866 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12866 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052140971943 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12866) ≤ 0.010528559607 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12866 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035575436502)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010528559607 + 2 * 0.737676 / 12866) := by gcongr
    _ ≤ (0.052140971943 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12866 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12866

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12866
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560510978447 : ℝ) ≤ plow 12866 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12866) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052573186925)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361954459) : eMP 12866 0.011 xi bn ≤ 0.001172735195 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12866 : ℝ) * (1 - 0.011))) ≤ 0.000579877602 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001361954459 / (12866 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579877602 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579877602 : ℝ) + 3.141593 * 0.052573186925 / (12866 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001172735195 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052573186925)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361954459) : PiBarMP 12866 12 0.011 xi bn ≤ 0.160196940761 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12866 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036904667171 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.802810248681 : ℝ) ≤ √((12866 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.428391507593 : ℝ) ≤ √(12866 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12866) ≤ 0.122829990601 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036904667171 + 0.052573186925 * 1.772454 / (2 * (112.802810248681 : ℝ))) * (1 + 0.001172735195) +
        8 / (12866 * 113.428391507593) + 0.122829990601 := by gcongr
    _ ≤ (0.160196940761 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052573186925)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361954459) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281429408034) :
    parallelOracle 12866 0.011 xi bn cd ≤ 0.161174377281 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12866 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12866 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560510978447 : ℝ) ≤ plow 12866 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.428391507593 : ℝ) ≤ √(12866 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281429408034 : ℝ) / (2 * 0.560510978447 * 113.428391507593)) * 0.160196940761 +
        0.281429408034 ^ 2 / (2 * 0.560510978447 * 113.428391507593) := by gcongr
    _ ≤ (0.161174377281 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052573186925) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361954459)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281429408034) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12866 12866 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560510978447 : ℝ) ≤ plow 12866 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.428391507593 : ℝ) ≤ √(12866 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12866 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12866 Θ 1.22 ≤ 0.011691080888 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.428391507593 := by gcongr <;> linarith
      _ ≤ (0.011691080888 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12866 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12866 12866 0.011 ≤ 0.008427228571 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12866 12866 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12866 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12866 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12866 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12866 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161174377281 + 0.011691080888 + (0.008427228571 : ℝ) *
        (1 + 2 * (0.281429408034 + 0.011691080888) / (0.560510978447 * 113.428391507593))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12866]

end BstLean.Part269.N12866

/-! The original eight local profiles supply actual 12866 moment certificates. -/
namespace BstLean.Part269.N12866
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12866 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12866 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12866 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052573186925 ∧
    0 ≤ bN 12866 BstLean.Part154.csC (groupTheta g) ∧ bN 12866 BstLean.Part154.csC (groupTheta g) ≤ 0.001361954459 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12866 12866 0.011
      (momentAllowance 12866 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12866 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12866 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12866 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12866 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12866 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229288436091 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12866 0.011
      (momentAllowance 12866 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12866 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12866
/-! The actual computed-centre upper energy formula at 12866. -/
namespace BstLean.Part269.N12866
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12866

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12866
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12866)
open BstLean.Part268 (cell12866)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085020291744
  | 2 => 0.085954718317
  | 3 => 0.086886121392
  | 4 => 0.087815647649
  | 5 => 0.088744692432
  | 6 => 0.089674937747
  | 7 => 0.090608394033
  | 8 => 0.091547445782
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12866 12866 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12866 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12866

/-! Actual upper energy certificates on all 43 source endpoints at 12866. -/
namespace BstLean.Part269.N12866
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12866)
open BstLean.Part268 (cell12866)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12866 (gMinus 12866) (1 - (cell12866 i).lower) ≤ 1 ∧
    energyUpper 12866 (gMinus 12866) (BstLean.Part211.gPlus 12866)
      (finiteEnergy 12866 12866 0.011) (1 - (cell12866 i).lower) ≤
      (cell12866 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨10,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨11,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨12,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨13,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨14,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨15,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨16,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨17,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨18,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨19,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨20,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨21,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨22,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨23,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨24,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨25,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨26,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨27,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨28,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨29,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨30,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨31,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨32,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨33,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨34,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨35,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨36,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨37,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨38,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨39,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨40,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨41,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨42,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨43,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨44,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨45,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨46,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨47,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨48,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨49,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨50,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨51,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12866) (by norm_num)
        (q := 1 - (cell12866 ⟨52,by decide⟩).lower)
        (by norm_num [cell12866]) (by norm_num [cell12866])
      exact ⟨E.1,E.2.trans (by norm_num [cell12866])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12866

/-! Source-cell containment and simple scalar guards at 12866. -/
namespace BstLean.Part269.N12866
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12866)
open BstLean.Part268 (cell12866)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12866 ⟨10,by decide⟩).lower ∧ (cell12866 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12866 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12866 ⟨11,by decide⟩).lower ∧ (cell12866 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12866 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12866 ⟨12,by decide⟩).lower ∧ (cell12866 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12866 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12866 ⟨13,by decide⟩).lower ∧ (cell12866 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12866 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12866 ⟨14,by decide⟩).lower ∧ (cell12866 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12866 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12866 ⟨15,by decide⟩).lower ∧ (cell12866 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12866 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12866 ⟨16,by decide⟩).lower ∧ (cell12866 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12866 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12866 ⟨17,by decide⟩).lower ∧ (cell12866 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12866 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12866 ⟨18,by decide⟩).lower ∧ (cell12866 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12866 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12866 ⟨19,by decide⟩).lower ∧ (cell12866 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12866 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12866 ⟨20,by decide⟩).lower ∧ (cell12866 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12866 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12866 ⟨21,by decide⟩).lower ∧ (cell12866 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12866 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12866 ⟨22,by decide⟩).lower ∧ (cell12866 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12866 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12866 ⟨23,by decide⟩).lower ∧ (cell12866 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12866 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12866 ⟨24,by decide⟩).lower ∧ (cell12866 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12866 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12866 ⟨25,by decide⟩).lower ∧ (cell12866 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12866 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12866 ⟨26,by decide⟩).lower ∧ (cell12866 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12866 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12866 ⟨27,by decide⟩).lower ∧ (cell12866 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12866 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12866 ⟨28,by decide⟩).lower ∧ (cell12866 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12866 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12866 ⟨29,by decide⟩).lower ∧ (cell12866 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12866 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12866 ⟨30,by decide⟩).lower ∧ (cell12866 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12866 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12866 ⟨31,by decide⟩).lower ∧ (cell12866 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12866 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12866 ⟨32,by decide⟩).lower ∧ (cell12866 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12866 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12866 ⟨33,by decide⟩).lower ∧ (cell12866 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12866 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12866 ⟨34,by decide⟩).lower ∧ (cell12866 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12866 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12866 ⟨35,by decide⟩).lower ∧ (cell12866 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12866 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12866 ⟨36,by decide⟩).lower ∧ (cell12866 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12866 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12866 ⟨37,by decide⟩).lower ∧ (cell12866 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12866 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12866 ⟨38,by decide⟩).lower ∧ (cell12866 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12866 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12866 ⟨39,by decide⟩).lower ∧ (cell12866 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12866 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12866 ⟨40,by decide⟩).lower ∧ (cell12866 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12866 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12866 ⟨41,by decide⟩).lower ∧ (cell12866 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12866 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12866 ⟨42,by decide⟩).lower ∧ (cell12866 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12866 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12866 ⟨43,by decide⟩).lower ∧ (cell12866 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12866 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12866 ⟨44,by decide⟩).lower ∧ (cell12866 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12866 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12866 ⟨45,by decide⟩).lower ∧ (cell12866 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12866 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12866 ⟨46,by decide⟩).lower ∧ (cell12866 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12866 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12866 ⟨47,by decide⟩).lower ∧ (cell12866 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12866 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12866 ⟨48,by decide⟩).lower ∧ (cell12866 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12866 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12866 ⟨49,by decide⟩).lower ∧ (cell12866 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12866 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12866 ⟨50,by decide⟩).lower ∧ (cell12866 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12866 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12866 ⟨51,by decide⟩).lower ∧ (cell12866 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12866 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12866 ⟨52,by decide⟩).lower ∧ (cell12866 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12866 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12866 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12866 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12866,cell12866,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12866 i).lower ∧
    (cell12866 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12866 i).upper ≤ (0.532 : ℝ) ∧
    (cell12866 i).centre ≤ (0.1 : ℝ) ∧ (cell12866 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12866 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12866 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12866

/-! The local source numeric instances at 12866 have no network premises. -/
namespace BstLean.Part269.N12866
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12866)
open BstLean.Part268 (cell12866)

noncomputable def sourceNumerics12866 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12866 (cell12866 i)
      scalarRow12866.M scalarRow12866.H scalarRow12866.xi := by
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
    energy_allowance := scalarRow12866.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12866]
    centre_nonneg := (scalarRow12866.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12866])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12866
/-! Actual 12867 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12867
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12867 ≤ (1.035574041965 : ℝ) := by
  have hr : (113.432799489389 : ℝ) ≤ √(12867 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.432799489389 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12867 12867 (11 / 1000) ≤
    (0.008426901088 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12867) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.432799489389 : ℝ) ≤ √(12867 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12867)
  have hdiv : K / √(12867 : ℝ) ≤ K / 113.432799489389 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.432799489389 ≤ (0.008426901088 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12867.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12867 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12867 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12867 := gPlus_lower 12867
end BstLean.Part269.N12867

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12867
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035574041964 : ℝ) ≤ wn 12867 := by
  have hn : √(12867 : ℝ) ≤ 113.432799489390 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12867 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.432799489390 ≤ 2 / √(12867 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248555276 : ℝ) ≤ rhoBar 12867 BstLean.Part154.csC ∧
    rhoBar 12867 BstLean.Part154.csC ≤ 0.000248555661 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035574041964 : ℝ) / (1.295212 * 12867) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035574041965 : ℝ) / (1.29521 * 12867) := by gcongr
      _ ≤ (0.000248555661 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12867 BstLean.Part154.csC) ≤ 0.000994284424 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12867 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12867 BstLean.Part154.csC) (piBar (rhoBar 12867 BstLean.Part154.csC)) ≤ 0.000189848374 ∧
    cc1 (rhoBar 12867 BstLean.Part154.csC) (piBar (rhoBar 12867 BstLean.Part154.csC)) ≤ 0.000120801805 ∧
    cc2 (rhoBar 12867 BstLean.Part154.csC) ≤ 0.000070126402 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12867 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12867 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12867 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12867 BstLean.Part154.csC * nuR (rhoBar 12867 BstLean.Part154.csC)) ≤ 0.000497126767 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248555661 : ℝ) * 0.000994284424 := by gcongr
      _ ≤ (0.000497126767 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12867 BstLean.Part154.csC) * nuR (rhoBar 12867 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000994284424 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12867 BstLean.Part154.csC) * rhoBar 12867 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248555661 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248555661 / 2 + 0.399 * 0.000994284424 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189848374 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497126767 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120801805 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248555661 / 1.414213562 := by gcongr
      _ ≤ (0.000070126402 : ℝ) := by norm_num

end BstLean.Part269.N12867

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12867
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12867 BstLean.Part154.csC) (piBar (rhoBar 12867 BstLean.Part154.csC)) ≤ 1.55650E-7 := by
  have hr0 : 0 ≤ rhoBar 12867 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12867 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12867 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12867 BstLean.Part154.csC) (piBar (rhoBar 12867 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12867 BstLean.Part154.csC) (piBar (rhoBar 12867 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12867 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189848374 : ℝ) ^ 2 + 0.000120801805 ^ 2 + 3 * 0.000070126402 ^ 2 +
        2 * 0.797885 * 0.000189848374 * 0.000120801805 + 2 * 0.000189848374 * 0.000070126402 +
        4 * 0.797885 * 0.000120801805 * 0.000070126402 := by gcongr
    _ ≤ (1.55650E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12867 BstLean.Part154.csC Θ ≤ 0.002593983958 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12867 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12867 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12867 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12867 BstLean.Part154.csC) (piBar (rhoBar 12867 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12867 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035574041965 * 1.55650E-7 / (0.000248555276 : ℝ) := by gcongr
    _ ≤ 0.002593983958 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12867 BstLean.Part154.csC Θ ≤ 0.002877510782 + 0.000655458228 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12867 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12867 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12867 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035574041965 : ℝ) * ((2 * Θ * 0.000248555661 +
        (6863 / 10000) * 0.000248555661 * 12867 * 0.000994284424) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002877510782 + 0.000655458228 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12867 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12867 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12867 0.011 Θ ∧ gammaRatio 12867 0.011 Θ ≤ 0.000085447009 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12867 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035574041965 : ℝ) * 0.525 / ((1 - 0.011) * 12867) := by gcongr
      _ ≤ (0.000085447009 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12867 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12867 0.011 Θ) :=
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
    badAllowance 12867 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12867 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12867 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12867 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12867 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12867 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12867 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12867 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12867 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12867 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12867 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035574041965 : ℝ) * 12867 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12867 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003360253944 + 0.003249442186 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12867

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12867
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12867 BstLean.Part154.csC) (piBar (rhoBar 12867 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12867 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12867 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12867 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12867 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12867 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12867 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12867 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12867 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12867 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12867 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12867 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12867 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12867 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12867 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052138923924 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12867) ≤ 0.010528150469 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12867 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035574041965)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010528150469 + 2 * 0.737676 / 12867) := by gcongr
    _ ≤ (0.052138923924 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12867 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12867

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12867
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511022507 : ℝ) ≤ plow 12867 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12867) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052572811092)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361841578) : eMP 12867 0.011 xi bn ≤ 0.001172640966 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12867 : ℝ) * (1 - 0.011))) ≤ 0.000579831038 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001361841578 / (12867 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579831038 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579831038 : ℝ) + 3.141593 * 0.052572811092 / (12867 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001172640966 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052572811092)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361841578) : PiBarMP 12867 12 0.011 xi bn ≤ 0.160190613241 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12867 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036903137780 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.807193919536 : ℝ) ≤ √((12867 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.432799489389 : ℝ) ≤ √(12867 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12867) ≤ 0.122825217446 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036903137780 + 0.052572811092 * 1.772454 / (2 * (112.807193919536 : ℝ))) * (1 + 0.001172640966) +
        8 / (12867 * 113.432799489389) + 0.122825217446 := by gcongr
    _ ≤ (0.160190613241 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052572811092)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361841578) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281426540450) :
    parallelOracle 12867 0.011 xi bn cd ≤ 0.161167981392 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12867 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12867 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511022507 : ℝ) ≤ plow 12867 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.432799489389 : ℝ) ≤ √(12867 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281426540450 : ℝ) / (2 * 0.560511022507 * 113.432799489389)) * 0.160190613241 +
        0.281426540450 ^ 2 / (2 * 0.560511022507 * 113.432799489389) := by gcongr
    _ ≤ (0.161167981392 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052572811092) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361841578)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281426540450) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12867 12867 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511022507 : ℝ) ≤ plow 12867 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.432799489389 : ℝ) ≤ √(12867 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12867 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12867 Θ 1.22 ≤ 0.011690626574 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.432799489389 := by gcongr <;> linarith
      _ ≤ (0.011690626574 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12867 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12867 12867 0.011 ≤ 0.008426901088 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12867 12867 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12867 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12867 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12867 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12867 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161167981392 + 0.011690626574 + (0.008426901088 : ℝ) *
        (1 + 2 * (0.281426540450 + 0.011690626574) / (0.560511022507 * 113.432799489389))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12867]

end BstLean.Part269.N12867

/-! The original eight local profiles supply actual 12867 moment certificates. -/
namespace BstLean.Part269.N12867
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12867 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12867 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12867 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052572811092 ∧
    0 ≤ bN 12867 BstLean.Part154.csC (groupTheta g) ∧ bN 12867 BstLean.Part154.csC (groupTheta g) ≤ 0.001361841578 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12867 12867 0.011
      (momentAllowance 12867 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12867 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12867 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12867 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12867 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12867 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229287616526 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12867 0.011
      (momentAllowance 12867 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12867 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12867
/-! The actual computed-centre upper energy formula at 12867. -/
namespace BstLean.Part269.N12867
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12867

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12867
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12867)
open BstLean.Part268 (cell12867)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085017541739
  | 2 => 0.085951921398
  | 3 => 0.086883271311
  | 4 => 0.087812736678
  | 5 => 0.088741711098
  | 6 => 0.089671874529
  | 7 => 0.090605235022
  | 8 => 0.091544174304
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12867 12867 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12867 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12867

/-! Actual upper energy certificates on all 43 source endpoints at 12867. -/
namespace BstLean.Part269.N12867
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12867)
open BstLean.Part268 (cell12867)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12867 (gMinus 12867) (1 - (cell12867 i).lower) ≤ 1 ∧
    energyUpper 12867 (gMinus 12867) (BstLean.Part211.gPlus 12867)
      (finiteEnergy 12867 12867 0.011) (1 - (cell12867 i).lower) ≤
      (cell12867 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨10,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨11,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨12,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨13,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨14,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨15,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨16,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨17,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨18,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨19,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨20,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨21,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨22,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨23,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨24,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨25,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨26,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨27,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨28,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨29,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨30,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨31,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨32,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨33,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨34,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨35,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨36,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨37,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨38,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨39,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨40,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨41,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨42,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨43,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨44,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨45,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨46,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨47,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨48,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨49,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨50,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨51,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12867) (by norm_num)
        (q := 1 - (cell12867 ⟨52,by decide⟩).lower)
        (by norm_num [cell12867]) (by norm_num [cell12867])
      exact ⟨E.1,E.2.trans (by norm_num [cell12867])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12867

/-! Source-cell containment and simple scalar guards at 12867. -/
namespace BstLean.Part269.N12867
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12867)
open BstLean.Part268 (cell12867)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12867 ⟨10,by decide⟩).lower ∧ (cell12867 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12867 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12867 ⟨11,by decide⟩).lower ∧ (cell12867 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12867 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12867 ⟨12,by decide⟩).lower ∧ (cell12867 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12867 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12867 ⟨13,by decide⟩).lower ∧ (cell12867 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12867 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12867 ⟨14,by decide⟩).lower ∧ (cell12867 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12867 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12867 ⟨15,by decide⟩).lower ∧ (cell12867 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12867 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12867 ⟨16,by decide⟩).lower ∧ (cell12867 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12867 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12867 ⟨17,by decide⟩).lower ∧ (cell12867 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12867 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12867 ⟨18,by decide⟩).lower ∧ (cell12867 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12867 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12867 ⟨19,by decide⟩).lower ∧ (cell12867 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12867 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12867 ⟨20,by decide⟩).lower ∧ (cell12867 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12867 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12867 ⟨21,by decide⟩).lower ∧ (cell12867 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12867 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12867 ⟨22,by decide⟩).lower ∧ (cell12867 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12867 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12867 ⟨23,by decide⟩).lower ∧ (cell12867 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12867 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12867 ⟨24,by decide⟩).lower ∧ (cell12867 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12867 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12867 ⟨25,by decide⟩).lower ∧ (cell12867 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12867 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12867 ⟨26,by decide⟩).lower ∧ (cell12867 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12867 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12867 ⟨27,by decide⟩).lower ∧ (cell12867 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12867 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12867 ⟨28,by decide⟩).lower ∧ (cell12867 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12867 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12867 ⟨29,by decide⟩).lower ∧ (cell12867 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12867 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12867 ⟨30,by decide⟩).lower ∧ (cell12867 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12867 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12867 ⟨31,by decide⟩).lower ∧ (cell12867 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12867 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12867 ⟨32,by decide⟩).lower ∧ (cell12867 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12867 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12867 ⟨33,by decide⟩).lower ∧ (cell12867 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12867 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12867 ⟨34,by decide⟩).lower ∧ (cell12867 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12867 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12867 ⟨35,by decide⟩).lower ∧ (cell12867 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12867 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12867 ⟨36,by decide⟩).lower ∧ (cell12867 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12867 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12867 ⟨37,by decide⟩).lower ∧ (cell12867 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12867 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12867 ⟨38,by decide⟩).lower ∧ (cell12867 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12867 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12867 ⟨39,by decide⟩).lower ∧ (cell12867 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12867 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12867 ⟨40,by decide⟩).lower ∧ (cell12867 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12867 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12867 ⟨41,by decide⟩).lower ∧ (cell12867 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12867 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12867 ⟨42,by decide⟩).lower ∧ (cell12867 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12867 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12867 ⟨43,by decide⟩).lower ∧ (cell12867 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12867 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12867 ⟨44,by decide⟩).lower ∧ (cell12867 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12867 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12867 ⟨45,by decide⟩).lower ∧ (cell12867 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12867 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12867 ⟨46,by decide⟩).lower ∧ (cell12867 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12867 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12867 ⟨47,by decide⟩).lower ∧ (cell12867 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12867 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12867 ⟨48,by decide⟩).lower ∧ (cell12867 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12867 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12867 ⟨49,by decide⟩).lower ∧ (cell12867 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12867 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12867 ⟨50,by decide⟩).lower ∧ (cell12867 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12867 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12867 ⟨51,by decide⟩).lower ∧ (cell12867 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12867 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12867 ⟨52,by decide⟩).lower ∧ (cell12867 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12867 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12867 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12867 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12867,cell12867,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12867 i).lower ∧
    (cell12867 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12867 i).upper ≤ (0.532 : ℝ) ∧
    (cell12867 i).centre ≤ (0.1 : ℝ) ∧ (cell12867 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12867 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12867 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12867

/-! The local source numeric instances at 12867 have no network premises. -/
namespace BstLean.Part269.N12867
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12867)
open BstLean.Part268 (cell12867)

noncomputable def sourceNumerics12867 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12867 (cell12867 i)
      scalarRow12867.M scalarRow12867.H scalarRow12867.xi := by
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
    energy_allowance := scalarRow12867.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12867]
    centre_nonneg := (scalarRow12867.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12867])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12867
/-! Actual 12868 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12868
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12868 ≤ (1.035572647591 : ℝ) := by
  have hr : (113.437207299897 : ℝ) ≤ √(12868 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.437207299897 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12868 12868 (11 / 1000) ≤
    (0.008426573643 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12868) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.437207299897 : ℝ) ≤ √(12868 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12868)
  have hdiv : K / √(12868 : ℝ) ≤ K / 113.437207299897 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.437207299897 ≤ (0.008426573643 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12868.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12868 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12868 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12868 := gPlus_lower 12868
end BstLean.Part269.N12868

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12868
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035572647590 : ℝ) ≤ wn 12868 := by
  have hn : √(12868 : ℝ) ≤ 113.437207299898 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12868 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.437207299898 ≤ 2 / √(12868 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248535625 : ℝ) ≤ rhoBar 12868 BstLean.Part154.csC ∧
    rhoBar 12868 BstLean.Part154.csC ≤ 0.000248536010 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035572647590 : ℝ) / (1.295212 * 12868) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035572647591 : ℝ) / (1.29521 * 12868) := by gcongr
      _ ≤ (0.000248536010 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12868 BstLean.Part154.csC) ≤ 0.000994205811 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12868 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12868 BstLean.Part154.csC) (piBar (rhoBar 12868 BstLean.Part154.csC)) ≤ 0.000189833364 ∧
    cc1 (rhoBar 12868 BstLean.Part154.csC) (piBar (rhoBar 12868 BstLean.Part154.csC)) ≤ 0.000120792254 ∧
    cc2 (rhoBar 12868 BstLean.Part154.csC) ≤ 0.000070120858 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12868 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12868 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12868 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12868 BstLean.Part154.csC * nuR (rhoBar 12868 BstLean.Part154.csC)) ≤ 0.000497087463 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248536010 : ℝ) * 0.000994205811 := by gcongr
      _ ≤ (0.000497087463 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12868 BstLean.Part154.csC) * nuR (rhoBar 12868 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000994205811 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12868 BstLean.Part154.csC) * rhoBar 12868 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248536010 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248536010 / 2 + 0.399 * 0.000994205811 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189833364 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497087463 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120792254 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248536010 / 1.414213562 := by gcongr
      _ ≤ (0.000070120858 : ℝ) := by norm_num

end BstLean.Part269.N12868

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12868
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12868 BstLean.Part154.csC) (piBar (rhoBar 12868 BstLean.Part154.csC)) ≤ 1.55626E-7 := by
  have hr0 : 0 ≤ rhoBar 12868 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12868 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12868 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12868 BstLean.Part154.csC) (piBar (rhoBar 12868 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12868 BstLean.Part154.csC) (piBar (rhoBar 12868 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12868 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189833364 : ℝ) ^ 2 + 0.000120792254 ^ 2 + 3 * 0.000070120858 ^ 2 +
        2 * 0.797885 * 0.000189833364 * 0.000120792254 + 2 * 0.000189833364 * 0.000070120858 +
        4 * 0.797885 * 0.000120792254 * 0.000070120858 := by gcongr
    _ ≤ (1.55626E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12868 BstLean.Part154.csC Θ ≤ 0.002593785561 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12868 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12868 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12868 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12868 BstLean.Part154.csC) (piBar (rhoBar 12868 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12868 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035572647591 * 1.55626E-7 / (0.000248535625 : ℝ) := by gcongr
    _ ≤ 0.002593785561 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12868 BstLean.Part154.csC Θ ≤ 0.002877275517 + 0.000655405525 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12868 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12868 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12868 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035572647591 : ℝ) * ((2 * Θ * 0.000248536010 +
        (6863 / 10000) * 0.000248536010 * 12868 * 0.000994205811) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002877275517 + 0.000655405525 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12868 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12868 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12868 0.011 Θ ∧ gammaRatio 12868 0.011 Θ ≤ 0.000085440254 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12868 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035572647591 : ℝ) * 0.525 / ((1 - 0.011) * 12868) := by gcongr
      _ ≤ (0.000085440254 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12868 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12868 0.011 Θ) :=
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
    badAllowance 12868 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12868 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12868 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12868 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12868 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12868 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12868 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12868 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12868 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12868 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12868 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035572647591 : ℝ) * 12868 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12868 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003360018679 + 0.003249191086 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12868

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12868
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12868 BstLean.Part154.csC) (piBar (rhoBar 12868 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12868 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12868 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12868 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12868 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12868 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12868 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12868 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12868 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12868 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12868 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12868 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12868 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12868 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12868 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052136876143 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12868) ≤ 0.010527741378 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12868 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035572647591)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010527741378 + 2 * 0.737676 / 12868) := by gcongr
    _ ≤ (0.052136876143 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12868 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12868

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12868
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511066560 : ℝ) ≤ plow 12868 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12868) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052572444000)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361737420) : eMP 12868 0.011 xi bn ≤ 0.001172550459 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12868 : ℝ) * (1 - 0.011))) ≤ 0.000579786334 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001361737420 / (12868 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579786334 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579786334 : ℝ) + 3.141593 * 0.052572444000 / (12868 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001172550459 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052572444000)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361737420) : PiBarMP 12868 12 0.011 xi bn ≤ 0.160184404754 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12868 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036901726518 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.811577420050 : ℝ) ≤ √((12868 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.437207299897 : ℝ) ≤ √(12868 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12868) ≤ 0.122820444847 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036901726518 + 0.052572444000 * 1.772454 / (2 * (112.811577420050 : ℝ))) * (1 + 0.001172550459) +
        8 / (12868 * 113.437207299897) + 0.122820444847 := by gcongr
    _ ≤ (0.160184404754 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052572444000)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361737420) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281423692162) :
    parallelOracle 12868 0.011 xi bn cd ≤ 0.161161704916 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12868 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12868 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511066560 : ℝ) ≤ plow 12868 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.437207299897 : ℝ) ≤ √(12868 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281423692162 : ℝ) / (2 * 0.560511066560 * 113.437207299897)) * 0.160184404754 +
        0.281423692162 ^ 2 / (2 * 0.560511066560 * 113.437207299897) := by gcongr
    _ ≤ (0.161161704916 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052572444000) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361737420)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281423692162) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12868 12868 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511066560 : ℝ) ≤ plow 12868 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.437207299897 : ℝ) ≤ √(12868 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12868 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12868 Θ 1.22 ≤ 0.011690172313 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.437207299897 := by gcongr <;> linarith
      _ ≤ (0.011690172313 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12868 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12868 12868 0.011 ≤ 0.008426573643 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12868 12868 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12868 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12868 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12868 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12868 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161161704916 + 0.011690172313 + (0.008426573643 : ℝ) *
        (1 + 2 * (0.281423692162 + 0.011690172313) / (0.560511066560 * 113.437207299897))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12868]

end BstLean.Part269.N12868

/-! The original eight local profiles supply actual 12868 moment certificates. -/
namespace BstLean.Part269.N12868
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12868 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12868 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12868 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052572444000 ∧
    0 ≤ bN 12868 BstLean.Part154.csC (groupTheta g) ∧ bN 12868 BstLean.Part154.csC (groupTheta g) ≤ 0.001361737420 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12868 12868 0.011
      (momentAllowance 12868 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12868 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12868 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12868 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12868 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12868 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229286816019 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12868 0.011
      (momentAllowance 12868 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12868 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12868
/-! The actual computed-centre upper energy formula at 12868. -/
namespace BstLean.Part269.N12868
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12868

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12868
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12868)
open BstLean.Part268 (cell12868)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085014792653
  | 2 => 0.085949125434
  | 3 => 0.086880422228
  | 4 => 0.087809826760
  | 5 => 0.088738730884
  | 6 => 0.089668812512
  | 7 => 0.090602077311
  | 8 => 0.091540904245
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12868 12868 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12868 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12868

/-! Actual upper energy certificates on all 43 source endpoints at 12868. -/
namespace BstLean.Part269.N12868
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12868)
open BstLean.Part268 (cell12868)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12868 (gMinus 12868) (1 - (cell12868 i).lower) ≤ 1 ∧
    energyUpper 12868 (gMinus 12868) (BstLean.Part211.gPlus 12868)
      (finiteEnergy 12868 12868 0.011) (1 - (cell12868 i).lower) ≤
      (cell12868 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨10,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨11,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨12,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨13,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨14,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨15,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨16,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨17,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨18,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨19,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨20,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨21,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨22,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨23,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨24,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨25,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨26,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨27,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨28,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨29,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨30,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨31,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨32,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨33,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨34,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨35,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨36,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨37,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨38,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨39,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨40,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨41,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨42,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨43,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨44,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨45,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨46,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨47,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨48,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨49,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨50,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨51,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12868) (by norm_num)
        (q := 1 - (cell12868 ⟨52,by decide⟩).lower)
        (by norm_num [cell12868]) (by norm_num [cell12868])
      exact ⟨E.1,E.2.trans (by norm_num [cell12868])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12868

/-! Source-cell containment and simple scalar guards at 12868. -/
namespace BstLean.Part269.N12868
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12868)
open BstLean.Part268 (cell12868)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12868 ⟨10,by decide⟩).lower ∧ (cell12868 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12868 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12868 ⟨11,by decide⟩).lower ∧ (cell12868 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12868 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12868 ⟨12,by decide⟩).lower ∧ (cell12868 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12868 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12868 ⟨13,by decide⟩).lower ∧ (cell12868 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12868 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12868 ⟨14,by decide⟩).lower ∧ (cell12868 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12868 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12868 ⟨15,by decide⟩).lower ∧ (cell12868 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12868 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12868 ⟨16,by decide⟩).lower ∧ (cell12868 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12868 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12868 ⟨17,by decide⟩).lower ∧ (cell12868 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12868 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12868 ⟨18,by decide⟩).lower ∧ (cell12868 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12868 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12868 ⟨19,by decide⟩).lower ∧ (cell12868 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12868 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12868 ⟨20,by decide⟩).lower ∧ (cell12868 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12868 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12868 ⟨21,by decide⟩).lower ∧ (cell12868 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12868 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12868 ⟨22,by decide⟩).lower ∧ (cell12868 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12868 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12868 ⟨23,by decide⟩).lower ∧ (cell12868 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12868 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12868 ⟨24,by decide⟩).lower ∧ (cell12868 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12868 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12868 ⟨25,by decide⟩).lower ∧ (cell12868 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12868 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12868 ⟨26,by decide⟩).lower ∧ (cell12868 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12868 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12868 ⟨27,by decide⟩).lower ∧ (cell12868 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12868 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12868 ⟨28,by decide⟩).lower ∧ (cell12868 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12868 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12868 ⟨29,by decide⟩).lower ∧ (cell12868 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12868 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12868 ⟨30,by decide⟩).lower ∧ (cell12868 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12868 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12868 ⟨31,by decide⟩).lower ∧ (cell12868 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12868 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12868 ⟨32,by decide⟩).lower ∧ (cell12868 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12868 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12868 ⟨33,by decide⟩).lower ∧ (cell12868 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12868 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12868 ⟨34,by decide⟩).lower ∧ (cell12868 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12868 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12868 ⟨35,by decide⟩).lower ∧ (cell12868 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12868 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12868 ⟨36,by decide⟩).lower ∧ (cell12868 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12868 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12868 ⟨37,by decide⟩).lower ∧ (cell12868 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12868 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12868 ⟨38,by decide⟩).lower ∧ (cell12868 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12868 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12868 ⟨39,by decide⟩).lower ∧ (cell12868 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12868 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12868 ⟨40,by decide⟩).lower ∧ (cell12868 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12868 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12868 ⟨41,by decide⟩).lower ∧ (cell12868 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12868 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12868 ⟨42,by decide⟩).lower ∧ (cell12868 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12868 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12868 ⟨43,by decide⟩).lower ∧ (cell12868 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12868 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12868 ⟨44,by decide⟩).lower ∧ (cell12868 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12868 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12868 ⟨45,by decide⟩).lower ∧ (cell12868 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12868 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12868 ⟨46,by decide⟩).lower ∧ (cell12868 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12868 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12868 ⟨47,by decide⟩).lower ∧ (cell12868 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12868 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12868 ⟨48,by decide⟩).lower ∧ (cell12868 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12868 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12868 ⟨49,by decide⟩).lower ∧ (cell12868 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12868 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12868 ⟨50,by decide⟩).lower ∧ (cell12868 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12868 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12868 ⟨51,by decide⟩).lower ∧ (cell12868 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12868 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12868 ⟨52,by decide⟩).lower ∧ (cell12868 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12868 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12868 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12868 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12868,cell12868,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12868 i).lower ∧
    (cell12868 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12868 i).upper ≤ (0.532 : ℝ) ∧
    (cell12868 i).centre ≤ (0.1 : ℝ) ∧ (cell12868 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12868 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12868 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12868

/-! The local source numeric instances at 12868 have no network premises. -/
namespace BstLean.Part269.N12868
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12868)
open BstLean.Part268 (cell12868)

noncomputable def sourceNumerics12868 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12868 (cell12868 i)
      scalarRow12868.M scalarRow12868.H scalarRow12868.xi := by
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
    energy_allowance := scalarRow12868.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12868]
    centre_nonneg := (scalarRow12868.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12868])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12868
/-! Actual 12869 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12869
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12869 ≤ (1.035571253381 : ℝ) := by
  have hr : (113.441614939139 : ℝ) ≤ √(12869 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.441614939139 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12869 12869 (11 / 1000) ≤
    (0.008426246236 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12869) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.441614939139 : ℝ) ≤ √(12869 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12869)
  have hdiv : K / √(12869 : ℝ) ≤ K / 113.441614939139 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.441614939139 ≤ (0.008426246236 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12869.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12869 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12869 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12869 := gPlus_lower 12869
end BstLean.Part269.N12869

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12869
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035571253380 : ℝ) ≤ wn 12869 := by
  have hn : √(12869 : ℝ) ≤ 113.441614939140 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12869 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.441614939140 ≤ 2 / √(12869 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248515978 : ℝ) ≤ rhoBar 12869 BstLean.Part154.csC ∧
    rhoBar 12869 BstLean.Part154.csC ≤ 0.000248516363 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035571253380 : ℝ) / (1.295212 * 12869) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035571253381 : ℝ) / (1.29521 * 12869) := by gcongr
      _ ≤ (0.000248516363 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12869 BstLean.Part154.csC) ≤ 0.000994127213 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12869 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12869 BstLean.Part154.csC) (piBar (rhoBar 12869 BstLean.Part154.csC)) ≤ 0.000189818357 ∧
    cc1 (rhoBar 12869 BstLean.Part154.csC) (piBar (rhoBar 12869 BstLean.Part154.csC)) ≤ 0.000120782705 ∧
    cc2 (rhoBar 12869 BstLean.Part154.csC) ≤ 0.000070115315 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12869 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12869 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12869 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12869 BstLean.Part154.csC * nuR (rhoBar 12869 BstLean.Part154.csC)) ≤ 0.000497048167 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248516363 : ℝ) * 0.000994127213 := by gcongr
      _ ≤ (0.000497048167 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12869 BstLean.Part154.csC) * nuR (rhoBar 12869 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000994127213 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12869 BstLean.Part154.csC) * rhoBar 12869 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248516363 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248516363 / 2 + 0.399 * 0.000994127213 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189818357 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497048167 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120782705 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248516363 / 1.414213562 := by gcongr
      _ ≤ (0.000070115315 : ℝ) := by norm_num

end BstLean.Part269.N12869

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12869
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12869 BstLean.Part154.csC) (piBar (rhoBar 12869 BstLean.Part154.csC)) ≤ 1.55601E-7 := by
  have hr0 : 0 ≤ rhoBar 12869 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12869 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12869 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12869 BstLean.Part154.csC) (piBar (rhoBar 12869 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12869 BstLean.Part154.csC) (piBar (rhoBar 12869 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12869 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189818357 : ℝ) ^ 2 + 0.000120782705 ^ 2 + 3 * 0.000070115315 ^ 2 +
        2 * 0.797885 * 0.000189818357 * 0.000120782705 + 2 * 0.000189818357 * 0.000070115315 +
        4 * 0.797885 * 0.000120782705 * 0.000070115315 := by gcongr
    _ ≤ (1.55601E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12869 BstLean.Part154.csC Θ ≤ 0.002593570424 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12869 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12869 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12869 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12869 BstLean.Part154.csC) (piBar (rhoBar 12869 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12869 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035571253381 * 1.55601E-7 / (0.000248515978 : ℝ) := by gcongr
    _ ≤ 0.002593570424 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12869 BstLean.Part154.csC Θ ≤ 0.002877040308 + 0.000655352832 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12869 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12869 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12869 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035571253381 : ℝ) * ((2 * Θ * 0.000248516363 +
        (6863 / 10000) * 0.000248516363 * 12869 * 0.000994127213) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002877040308 + 0.000655352832 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12869 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12869 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12869 0.011 Θ ∧ gammaRatio 12869 0.011 Θ ≤ 0.000085433499 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12869 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035571253381 : ℝ) * 0.525 / ((1 - 0.011) * 12869) := by gcongr
      _ ≤ (0.000085433499 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12869 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12869 0.011 Θ) :=
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
    badAllowance 12869 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12869 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12869 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12869 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12869 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12869 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12869 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12869 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12869 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12869 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12869 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035571253381 : ℝ) * 12869 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12869 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003359783470 + 0.003248923256 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12869

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12869
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12869 BstLean.Part154.csC) (piBar (rhoBar 12869 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12869 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12869 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12869 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12869 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12869 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12869 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12869 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12869 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12869 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12869 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12869 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12869 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12869 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12869 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052134828603 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12869) ≤ 0.010527332335 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12869 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035571253381)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010527332335 + 2 * 0.737676 / 12869) := by gcongr
    _ ≤ (0.052134828603 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12869 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12869

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12869
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511110606 : ℝ) ≤ plow 12869 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12869) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052572068180)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361624473) : eMP 12869 0.011 xi bn ≤ 0.001172456215 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12869 : ℝ) * (1 - 0.011))) ≤ 0.000579739763 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001361624473 / (12869 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579739763 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579739763 : ℝ) + 3.141593 * 0.052572068180 / (12869 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001172456215 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052572068180)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361624473) : PiBarMP 12869 12 0.011 xi bn ≤ 0.160178077334 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12869 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036900196111 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.815960750241 : ℝ) ≤ √((12869 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.441614939139 : ℝ) ≤ √(12869 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12869) ≤ 0.122815672805 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036900196111 + 0.052572068180 * 1.772454 / (2 * (112.815960750241 : ℝ))) * (1 + 0.001172456215) +
        8 / (12869 * 113.441614939139) + 0.122815672805 := by gcongr
    _ ≤ (0.160178077334 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052572068180)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361624473) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281420825080) :
    parallelOracle 12869 0.011 xi bn cd ≤ 0.161155309145 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12869 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12869 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511110606 : ℝ) ≤ plow 12869 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.441614939139 : ℝ) ≤ √(12869 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281420825080 : ℝ) / (2 * 0.560511110606 * 113.441614939139)) * 0.160178077334 +
        0.281420825080 ^ 2 / (2 * 0.560511110606 * 113.441614939139) := by gcongr
    _ ≤ (0.161155309145 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052572068180) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361624473)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281420825080) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12869 12869 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511110606 : ℝ) ≤ plow 12869 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.441614939139 : ℝ) ≤ √(12869 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12869 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12869 Θ 1.22 ≤ 0.011689718105 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.441614939139 := by gcongr <;> linarith
      _ ≤ (0.011689718105 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12869 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12869 12869 0.011 ≤ 0.008426246236 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12869 12869 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12869 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12869 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12869 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12869 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161155309145 + 0.011689718105 + (0.008426246236 : ℝ) *
        (1 + 2 * (0.281420825080 + 0.011689718105) / (0.560511110606 * 113.441614939139))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12869]

end BstLean.Part269.N12869

/-! The original eight local profiles supply actual 12869 moment certificates. -/
namespace BstLean.Part269.N12869
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12869 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12869 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12869 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052572068180 ∧
    0 ≤ bN 12869 BstLean.Part154.csC (groupTheta g) ∧ bN 12869 BstLean.Part154.csC (groupTheta g) ≤ 0.001361624473 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12869 12869 0.011
      (momentAllowance 12869 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12869 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12869 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12869 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12869 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12869 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229285996477 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12869 0.011
      (momentAllowance 12869 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12869 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12869
/-! The actual computed-centre upper energy formula at 12869. -/
namespace BstLean.Part269.N12869
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12869

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12869
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12869)
open BstLean.Part268 (cell12869)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085012044486
  | 2 => 0.085946330424
  | 3 => 0.086877574144
  | 4 => 0.087806917895
  | 5 => 0.088735751789
  | 6 => 0.089665751695
  | 7 => 0.090598920898
  | 8 => 0.091537635603
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12869 12869 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12869 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12869

/-! Actual upper energy certificates on all 43 source endpoints at 12869. -/
namespace BstLean.Part269.N12869
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12869)
open BstLean.Part268 (cell12869)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12869 (gMinus 12869) (1 - (cell12869 i).lower) ≤ 1 ∧
    energyUpper 12869 (gMinus 12869) (BstLean.Part211.gPlus 12869)
      (finiteEnergy 12869 12869 0.011) (1 - (cell12869 i).lower) ≤
      (cell12869 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨10,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨11,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨12,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨13,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨14,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨15,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨16,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨17,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨18,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨19,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨20,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨21,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨22,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨23,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨24,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨25,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨26,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨27,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨28,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨29,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨30,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨31,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨32,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨33,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨34,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨35,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨36,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨37,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨38,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨39,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨40,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨41,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨42,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨43,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨44,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨45,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨46,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨47,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨48,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨49,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨50,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨51,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12869) (by norm_num)
        (q := 1 - (cell12869 ⟨52,by decide⟩).lower)
        (by norm_num [cell12869]) (by norm_num [cell12869])
      exact ⟨E.1,E.2.trans (by norm_num [cell12869])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12869

/-! Source-cell containment and simple scalar guards at 12869. -/
namespace BstLean.Part269.N12869
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12869)
open BstLean.Part268 (cell12869)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12869 ⟨10,by decide⟩).lower ∧ (cell12869 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12869 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12869 ⟨11,by decide⟩).lower ∧ (cell12869 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12869 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12869 ⟨12,by decide⟩).lower ∧ (cell12869 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12869 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12869 ⟨13,by decide⟩).lower ∧ (cell12869 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12869 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12869 ⟨14,by decide⟩).lower ∧ (cell12869 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12869 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12869 ⟨15,by decide⟩).lower ∧ (cell12869 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12869 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12869 ⟨16,by decide⟩).lower ∧ (cell12869 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12869 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12869 ⟨17,by decide⟩).lower ∧ (cell12869 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12869 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12869 ⟨18,by decide⟩).lower ∧ (cell12869 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12869 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12869 ⟨19,by decide⟩).lower ∧ (cell12869 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12869 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12869 ⟨20,by decide⟩).lower ∧ (cell12869 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12869 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12869 ⟨21,by decide⟩).lower ∧ (cell12869 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12869 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12869 ⟨22,by decide⟩).lower ∧ (cell12869 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12869 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12869 ⟨23,by decide⟩).lower ∧ (cell12869 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12869 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12869 ⟨24,by decide⟩).lower ∧ (cell12869 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12869 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12869 ⟨25,by decide⟩).lower ∧ (cell12869 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12869 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12869 ⟨26,by decide⟩).lower ∧ (cell12869 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12869 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12869 ⟨27,by decide⟩).lower ∧ (cell12869 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12869 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12869 ⟨28,by decide⟩).lower ∧ (cell12869 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12869 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12869 ⟨29,by decide⟩).lower ∧ (cell12869 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12869 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12869 ⟨30,by decide⟩).lower ∧ (cell12869 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12869 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12869 ⟨31,by decide⟩).lower ∧ (cell12869 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12869 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12869 ⟨32,by decide⟩).lower ∧ (cell12869 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12869 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12869 ⟨33,by decide⟩).lower ∧ (cell12869 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12869 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12869 ⟨34,by decide⟩).lower ∧ (cell12869 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12869 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12869 ⟨35,by decide⟩).lower ∧ (cell12869 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12869 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12869 ⟨36,by decide⟩).lower ∧ (cell12869 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12869 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12869 ⟨37,by decide⟩).lower ∧ (cell12869 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12869 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12869 ⟨38,by decide⟩).lower ∧ (cell12869 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12869 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12869 ⟨39,by decide⟩).lower ∧ (cell12869 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12869 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12869 ⟨40,by decide⟩).lower ∧ (cell12869 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12869 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12869 ⟨41,by decide⟩).lower ∧ (cell12869 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12869 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12869 ⟨42,by decide⟩).lower ∧ (cell12869 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12869 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12869 ⟨43,by decide⟩).lower ∧ (cell12869 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12869 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12869 ⟨44,by decide⟩).lower ∧ (cell12869 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12869 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12869 ⟨45,by decide⟩).lower ∧ (cell12869 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12869 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12869 ⟨46,by decide⟩).lower ∧ (cell12869 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12869 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12869 ⟨47,by decide⟩).lower ∧ (cell12869 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12869 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12869 ⟨48,by decide⟩).lower ∧ (cell12869 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12869 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12869 ⟨49,by decide⟩).lower ∧ (cell12869 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12869 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12869 ⟨50,by decide⟩).lower ∧ (cell12869 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12869 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12869 ⟨51,by decide⟩).lower ∧ (cell12869 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12869 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12869 ⟨52,by decide⟩).lower ∧ (cell12869 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12869 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12869 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12869 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12869,cell12869,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12869 i).lower ∧
    (cell12869 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12869 i).upper ≤ (0.532 : ℝ) ∧
    (cell12869 i).centre ≤ (0.1 : ℝ) ∧ (cell12869 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12869 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12869 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12869

/-! The local source numeric instances at 12869 have no network premises. -/
namespace BstLean.Part269.N12869
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12869)
open BstLean.Part268 (cell12869)

noncomputable def sourceNumerics12869 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12869 (cell12869 i)
      scalarRow12869.M scalarRow12869.H scalarRow12869.xi := by
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
    energy_allowance := scalarRow12869.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12869]
    centre_nonneg := (scalarRow12869.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12869])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12869
/-! Actual 12870 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12870
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12870 ≤ (1.035569859334 : ℝ) := by
  have hr : (113.446022407134 : ℝ) ≤ √(12870 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.446022407134 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12870 12870 (11 / 1000) ≤
    (0.008425918867 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12870) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.446022407134 : ℝ) ≤ √(12870 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12870)
  have hdiv : K / √(12870 : ℝ) ≤ K / 113.446022407134 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.446022407134 ≤ (0.008425918867 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12870.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12870 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12870 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12870 := gPlus_lower 12870
end BstLean.Part269.N12870

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12870
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035569859333 : ℝ) ≤ wn 12870 := by
  have hn : √(12870 : ℝ) ≤ 113.446022407135 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12870 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.446022407135 ≤ 2 / √(12870 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248496334 : ℝ) ≤ rhoBar 12870 BstLean.Part154.csC ∧
    rhoBar 12870 BstLean.Part154.csC ≤ 0.000248496719 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035569859333 : ℝ) / (1.295212 * 12870) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035569859334 : ℝ) / (1.29521 * 12870) := by gcongr
      _ ≤ (0.000248496719 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12870 BstLean.Part154.csC) ≤ 0.000994048627 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12870 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12870 BstLean.Part154.csC) (piBar (rhoBar 12870 BstLean.Part154.csC)) ≤ 0.000189803352 ∧
    cc1 (rhoBar 12870 BstLean.Part154.csC) (piBar (rhoBar 12870 BstLean.Part154.csC)) ≤ 0.000120773157 ∧
    cc2 (rhoBar 12870 BstLean.Part154.csC) ≤ 0.000070109773 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12870 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12870 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12870 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12870 BstLean.Part154.csC * nuR (rhoBar 12870 BstLean.Part154.csC)) ≤ 0.000497008876 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248496719 : ℝ) * 0.000994048627 := by gcongr
      _ ≤ (0.000497008876 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12870 BstLean.Part154.csC) * nuR (rhoBar 12870 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000994048627 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12870 BstLean.Part154.csC) * rhoBar 12870 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248496719 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248496719 / 2 + 0.399 * 0.000994048627 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189803352 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000497008876 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120773157 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248496719 / 1.414213562 := by gcongr
      _ ≤ (0.000070109773 : ℝ) := by norm_num

end BstLean.Part269.N12870

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12870
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12870 BstLean.Part154.csC) (piBar (rhoBar 12870 BstLean.Part154.csC)) ≤ 1.55576E-7 := by
  have hr0 : 0 ≤ rhoBar 12870 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12870 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12870 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12870 BstLean.Part154.csC) (piBar (rhoBar 12870 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12870 BstLean.Part154.csC) (piBar (rhoBar 12870 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12870 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189803352 : ℝ) ^ 2 + 0.000120773157 ^ 2 + 3 * 0.000070109773 ^ 2 +
        2 * 0.797885 * 0.000189803352 * 0.000120773157 + 2 * 0.000189803352 * 0.000070109773 +
        4 * 0.797885 * 0.000120773157 * 0.000070109773 := by gcongr
    _ ≤ (1.55576E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12870 BstLean.Part154.csC Θ ≤ 0.002593355224 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12870 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12870 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12870 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12870 BstLean.Part154.csC) (piBar (rhoBar 12870 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12870 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035569859334 * 1.55576E-7 / (0.000248496334 : ℝ) := by gcongr
    _ ≤ 0.002593355224 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12870 BstLean.Part154.csC Θ ≤ 0.002876805135 + 0.000655300147 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12870 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12870 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12870 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035569859334 : ℝ) * ((2 * Θ * 0.000248496719 +
        (6863 / 10000) * 0.000248496719 * 12870 * 0.000994048627) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002876805135 + 0.000655300147 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12870 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12870 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12870 0.011 Θ ∧ gammaRatio 12870 0.011 Θ ≤ 0.000085426746 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12870 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035569859334 : ℝ) * 0.525 / ((1 - 0.011) * 12870) := by gcongr
      _ ≤ (0.000085426746 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12870 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12870 0.011 Θ) :=
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
    badAllowance 12870 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12870 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12870 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12870 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12870 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12870 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12870 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12870 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12870 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12870 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12870 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035569859334 : ℝ) * 12870 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12870 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003359548297 + 0.003248655371 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12870

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12870
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12870 BstLean.Part154.csC) (piBar (rhoBar 12870 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12870 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12870 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12870 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12870 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12870 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12870 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12870 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12870 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12870 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12870 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12870 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12870 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12870 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12870 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052132781306 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12870) ≤ 0.010526923340 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12870 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035569859334)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010526923340 + 2 * 0.737676 / 12870) := by gcongr
    _ ≤ (0.052132781306 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12870 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12870

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12870
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511154646 : ℝ) ≤ plow 12870 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12870) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052571692367)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361511493) : eMP 12870 0.011 xi bn ≤ 0.001172361964 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12870 : ℝ) * (1 - 0.011))) ≤ 0.000579693188 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001361511493 / (12870 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579693188 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579693188 : ℝ) + 3.141593 * 0.052571692367 / (12870 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001172361964 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052571692367)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361511493) : PiBarMP 12870 12 0.011 xi bn ≤ 0.160171749960 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12870 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036898665193 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.820343910129 : ℝ) ≤ √((12870 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.446022407134 : ℝ) ≤ √(12870 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12870) ≤ 0.122810901318 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036898665193 + 0.052571692367 * 1.772454 / (2 * (112.820343910129 : ℝ))) * (1 + 0.001172361964) +
        8 / (12870 * 113.446022407134) + 0.122810901318 := by gcongr
    _ ≤ (0.160171749960 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052571692367)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361511493) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281417958252) :
    parallelOracle 12870 0.011 xi bn cd ≤ 0.161148913428 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12870 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12870 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511154646 : ℝ) ≤ plow 12870 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.446022407134 : ℝ) ≤ √(12870 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281417958252 : ℝ) / (2 * 0.560511154646 * 113.446022407134)) * 0.160171749960 +
        0.281417958252 ^ 2 / (2 * 0.560511154646 * 113.446022407134) := by gcongr
    _ ≤ (0.161148913428 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052571692367) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361511493)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281417958252) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12870 12870 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511154646 : ℝ) ≤ plow 12870 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.446022407134 : ℝ) ≤ √(12870 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12870 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12870 Θ 1.22 ≤ 0.011689263951 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.446022407134 := by gcongr <;> linarith
      _ ≤ (0.011689263951 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12870 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12870 12870 0.011 ≤ 0.008425918867 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12870 12870 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12870 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12870 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12870 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12870 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161148913428 + 0.011689263951 + (0.008425918867 : ℝ) *
        (1 + 2 * (0.281417958252 + 0.011689263951) / (0.560511154646 * 113.446022407134))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12870]

end BstLean.Part269.N12870

/-! The original eight local profiles supply actual 12870 moment certificates. -/
namespace BstLean.Part269.N12870
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12870 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12870 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12870 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052571692367 ∧
    0 ≤ bN 12870 BstLean.Part154.csC (groupTheta g) ∧ bN 12870 BstLean.Part154.csC (groupTheta g) ≤ 0.001361511493 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12870 12870 0.011
      (momentAllowance 12870 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12870 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12870 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12870 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12870 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12870 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229285176946 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12870 0.011
      (momentAllowance 12870 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12870 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12870
/-! The actual computed-centre upper energy formula at 12870. -/
namespace BstLean.Part269.N12870
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12870

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12870
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12870)
open BstLean.Part268 (cell12870)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085009297235
  | 2 => 0.085943536366
  | 3 => 0.086874727057
  | 4 => 0.087804010081
  | 5 => 0.088732773812
  | 6 => 0.089662692078
  | 7 => 0.090595765783
  | 8 => 0.091534368377
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12870 12870 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12870 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12870

/-! Actual upper energy certificates on all 43 source endpoints at 12870. -/
namespace BstLean.Part269.N12870
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12870)
open BstLean.Part268 (cell12870)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12870 (gMinus 12870) (1 - (cell12870 i).lower) ≤ 1 ∧
    energyUpper 12870 (gMinus 12870) (BstLean.Part211.gPlus 12870)
      (finiteEnergy 12870 12870 0.011) (1 - (cell12870 i).lower) ≤
      (cell12870 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨10,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨11,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨12,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨13,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨14,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨15,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨16,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨17,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨18,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨19,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨20,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨21,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨22,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨23,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨24,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨25,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨26,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨27,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨28,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨29,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨30,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨31,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨32,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨33,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨34,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨35,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨36,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨37,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨38,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨39,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨40,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨41,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨42,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨43,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨44,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨45,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨46,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨47,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨48,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨49,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨50,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨51,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12870) (by norm_num)
        (q := 1 - (cell12870 ⟨52,by decide⟩).lower)
        (by norm_num [cell12870]) (by norm_num [cell12870])
      exact ⟨E.1,E.2.trans (by norm_num [cell12870])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12870

/-! Source-cell containment and simple scalar guards at 12870. -/
namespace BstLean.Part269.N12870
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12870)
open BstLean.Part268 (cell12870)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12870 ⟨10,by decide⟩).lower ∧ (cell12870 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12870 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12870 ⟨11,by decide⟩).lower ∧ (cell12870 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12870 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12870 ⟨12,by decide⟩).lower ∧ (cell12870 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12870 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12870 ⟨13,by decide⟩).lower ∧ (cell12870 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12870 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12870 ⟨14,by decide⟩).lower ∧ (cell12870 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12870 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12870 ⟨15,by decide⟩).lower ∧ (cell12870 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12870 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12870 ⟨16,by decide⟩).lower ∧ (cell12870 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12870 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12870 ⟨17,by decide⟩).lower ∧ (cell12870 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12870 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12870 ⟨18,by decide⟩).lower ∧ (cell12870 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12870 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12870 ⟨19,by decide⟩).lower ∧ (cell12870 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12870 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12870 ⟨20,by decide⟩).lower ∧ (cell12870 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12870 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12870 ⟨21,by decide⟩).lower ∧ (cell12870 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12870 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12870 ⟨22,by decide⟩).lower ∧ (cell12870 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12870 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12870 ⟨23,by decide⟩).lower ∧ (cell12870 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12870 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12870 ⟨24,by decide⟩).lower ∧ (cell12870 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12870 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12870 ⟨25,by decide⟩).lower ∧ (cell12870 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12870 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12870 ⟨26,by decide⟩).lower ∧ (cell12870 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12870 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12870 ⟨27,by decide⟩).lower ∧ (cell12870 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12870 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12870 ⟨28,by decide⟩).lower ∧ (cell12870 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12870 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12870 ⟨29,by decide⟩).lower ∧ (cell12870 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12870 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12870 ⟨30,by decide⟩).lower ∧ (cell12870 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12870 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12870 ⟨31,by decide⟩).lower ∧ (cell12870 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12870 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12870 ⟨32,by decide⟩).lower ∧ (cell12870 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12870 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12870 ⟨33,by decide⟩).lower ∧ (cell12870 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12870 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12870 ⟨34,by decide⟩).lower ∧ (cell12870 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12870 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12870 ⟨35,by decide⟩).lower ∧ (cell12870 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12870 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12870 ⟨36,by decide⟩).lower ∧ (cell12870 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12870 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12870 ⟨37,by decide⟩).lower ∧ (cell12870 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12870 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12870 ⟨38,by decide⟩).lower ∧ (cell12870 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12870 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12870 ⟨39,by decide⟩).lower ∧ (cell12870 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12870 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12870 ⟨40,by decide⟩).lower ∧ (cell12870 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12870 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12870 ⟨41,by decide⟩).lower ∧ (cell12870 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12870 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12870 ⟨42,by decide⟩).lower ∧ (cell12870 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12870 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12870 ⟨43,by decide⟩).lower ∧ (cell12870 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12870 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12870 ⟨44,by decide⟩).lower ∧ (cell12870 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12870 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12870 ⟨45,by decide⟩).lower ∧ (cell12870 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12870 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12870 ⟨46,by decide⟩).lower ∧ (cell12870 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12870 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12870 ⟨47,by decide⟩).lower ∧ (cell12870 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12870 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12870 ⟨48,by decide⟩).lower ∧ (cell12870 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12870 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12870 ⟨49,by decide⟩).lower ∧ (cell12870 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12870 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12870 ⟨50,by decide⟩).lower ∧ (cell12870 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12870 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12870 ⟨51,by decide⟩).lower ∧ (cell12870 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12870 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12870 ⟨52,by decide⟩).lower ∧ (cell12870 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12870 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12870 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12870 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12870,cell12870,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12870 i).lower ∧
    (cell12870 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12870 i).upper ≤ (0.532 : ℝ) ∧
    (cell12870 i).centre ≤ (0.1 : ℝ) ∧ (cell12870 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12870 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12870 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12870

/-! The local source numeric instances at 12870 have no network premises. -/
namespace BstLean.Part269.N12870
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12870)
open BstLean.Part268 (cell12870)

noncomputable def sourceNumerics12870 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12870 (cell12870 i)
      scalarRow12870.M scalarRow12870.H scalarRow12870.xi := by
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
    energy_allowance := scalarRow12870.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12870]
    centre_nonneg := (scalarRow12870.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12870])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12870
/-! Actual 12871 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12871
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12871 ≤ (1.035568465451 : ℝ) := by
  have hr : (113.450429703901 : ℝ) ≤ √(12871 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.450429703901 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12871 12871 (11 / 1000) ≤
    (0.008425591536 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12871) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.450429703901 : ℝ) ≤ √(12871 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12871)
  have hdiv : K / √(12871 : ℝ) ≤ K / 113.450429703901 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.450429703901 ≤ (0.008425591536 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12871.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12871 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12871 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12871 := gPlus_lower 12871
end BstLean.Part269.N12871

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12871
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035568465450 : ℝ) ≤ wn 12871 := by
  have hn : √(12871 : ℝ) ≤ 113.450429703902 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12871 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.450429703902 ≤ 2 / √(12871 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248476693 : ℝ) ≤ rhoBar 12871 BstLean.Part154.csC ∧
    rhoBar 12871 BstLean.Part154.csC ≤ 0.000248477077 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035568465450 : ℝ) / (1.295212 * 12871) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035568465451 : ℝ) / (1.29521 * 12871) := by gcongr
      _ ≤ (0.000248477077 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12871 BstLean.Part154.csC) ≤ 0.000993970049 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12871 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12871 BstLean.Part154.csC) (piBar (rhoBar 12871 BstLean.Part154.csC)) ≤ 0.000189788348 ∧
    cc1 (rhoBar 12871 BstLean.Part154.csC) (piBar (rhoBar 12871 BstLean.Part154.csC)) ≤ 0.000120763611 ∧
    cc2 (rhoBar 12871 BstLean.Part154.csC) ≤ 0.000070104231 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12871 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12871 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12871 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12871 BstLean.Part154.csC * nuR (rhoBar 12871 BstLean.Part154.csC)) ≤ 0.000496969590 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248477077 : ℝ) * 0.000993970049 := by gcongr
      _ ≤ (0.000496969590 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12871 BstLean.Part154.csC) * nuR (rhoBar 12871 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000993970049 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12871 BstLean.Part154.csC) * rhoBar 12871 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248477077 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248477077 / 2 + 0.399 * 0.000993970049 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189788348 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496969590 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120763611 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248477077 / 1.414213562 := by gcongr
      _ ≤ (0.000070104231 : ℝ) := by norm_num

end BstLean.Part269.N12871

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12871
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12871 BstLean.Part154.csC) (piBar (rhoBar 12871 BstLean.Part154.csC)) ≤ 1.55552E-7 := by
  have hr0 : 0 ≤ rhoBar 12871 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12871 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12871 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12871 BstLean.Part154.csC) (piBar (rhoBar 12871 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12871 BstLean.Part154.csC) (piBar (rhoBar 12871 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12871 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189788348 : ℝ) ^ 2 + 0.000120763611 ^ 2 + 3 * 0.000070104231 ^ 2 +
        2 * 0.797885 * 0.000189788348 * 0.000120763611 + 2 * 0.000189788348 * 0.000070104231 +
        4 * 0.797885 * 0.000120763611 * 0.000070104231 := by gcongr
    _ ≤ (1.55552E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12871 BstLean.Part154.csC Θ ≤ 0.002593156630 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12871 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12871 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12871 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12871 BstLean.Part154.csC) (piBar (rhoBar 12871 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12871 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035568465451 * 1.55552E-7 / (0.000248476693 : ℝ) := by gcongr
    _ ≤ 0.002593156630 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12871 BstLean.Part154.csC Θ ≤ 0.002876569974 + 0.000655247468 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12871 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12871 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12871 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035568465451 : ℝ) * ((2 * Θ * 0.000248477077 +
        (6863 / 10000) * 0.000248477077 * 12871 * 0.000993970049) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002876569974 + 0.000655247468 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12871 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12871 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12871 0.011 Θ ∧ gammaRatio 12871 0.011 Θ ≤ 0.000085419994 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12871 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035568465451 : ℝ) * 0.525 / ((1 - 0.011) * 12871) := by gcongr
      _ ≤ (0.000085419994 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12871 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12871 0.011 Θ) :=
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
    badAllowance 12871 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12871 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12871 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12871 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12871 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12871 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12871 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12871 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12871 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12871 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12871 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035568465451 : ℝ) * 12871 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12871 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003359313136 + 0.003248404098 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12871

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12871
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12871 BstLean.Part154.csC) (piBar (rhoBar 12871 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12871 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12871 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12871 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12871 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12871 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12871 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12871 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12871 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12871 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12871 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12871 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12871 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12871 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12871 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052130734245 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12871) ≤ 0.010526514392 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12871 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035568465451)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010526514392 + 2 * 0.737676 / 12871) := by gcongr
    _ ≤ (0.052130734245 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12871 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12871

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12871
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511198679 : ℝ) ≤ plow 12871 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12871) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052571325288)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361407231) : eMP 12871 0.011 xi bn ≤ 0.001172271436 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12871 : ℝ) * (1 - 0.011))) ≤ 0.000579648473 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001361407231 / (12871 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579648473 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579648473 : ℝ) + 3.141593 * 0.052571325288 / (12871 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001172271436 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052571325288)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361407231) : PiBarMP 12871 12 0.011 xi bn ≤ 0.160165541567 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12871 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036897252351 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.824726899735 : ℝ) ≤ √((12871 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.450429703901 : ℝ) ≤ √(12871 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12871) ≤ 0.122806130388 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036897252351 + 0.052571325288 * 1.772454 / (2 * (112.824726899735 : ℝ))) * (1 + 0.001172271436) +
        8 / (12871 * 113.450429703901) + 0.122806130388 := by gcongr
    _ ≤ (0.160165541567 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052571325288)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361407231) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281415110704) :
    parallelOracle 12871 0.011 xi bn cd ≤ 0.161142637072 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12871 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12871 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511198679 : ℝ) ≤ plow 12871 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.450429703901 : ℝ) ≤ √(12871 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281415110704 : ℝ) / (2 * 0.560511198679 * 113.450429703901)) * 0.160165541567 +
        0.281415110704 ^ 2 / (2 * 0.560511198679 * 113.450429703901) := by gcongr
    _ ≤ (0.161142637072 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052571325288) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361407231)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281415110704) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12871 12871 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511198679 : ℝ) ≤ plow 12871 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.450429703901 : ℝ) ≤ √(12871 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12871 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12871 Θ 1.22 ≤ 0.011688809849 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.450429703901 := by gcongr <;> linarith
      _ ≤ (0.011688809849 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12871 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12871 12871 0.011 ≤ 0.008425591536 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12871 12871 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12871 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12871 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12871 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12871 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161142637072 + 0.011688809849 + (0.008425591536 : ℝ) *
        (1 + 2 * (0.281415110704 + 0.011688809849) / (0.560511198679 * 113.450429703901))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12871]

end BstLean.Part269.N12871

/-! The original eight local profiles supply actual 12871 moment certificates. -/
namespace BstLean.Part269.N12871
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12871 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12871 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12871 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052571325288 ∧
    0 ≤ bN 12871 BstLean.Part154.csC (groupTheta g) ∧ bN 12871 BstLean.Part154.csC (groupTheta g) ≤ 0.001361407231 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12871 12871 0.011
      (momentAllowance 12871 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12871 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12871 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12871 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12871 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12871 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229284376459 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12871 0.011
      (momentAllowance 12871 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12871 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12871
/-! The actual computed-centre upper energy formula at 12871. -/
namespace BstLean.Part269.N12871
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12871

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12871
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12871)
open BstLean.Part268 (cell12871)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085006550900
  | 2 => 0.085940743261
  | 3 => 0.086871880965
  | 4 => 0.087801103318
  | 5 => 0.088729796952
  | 6 => 0.089659633658
  | 7 => 0.090592611964
  | 8 => 0.091531102566
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12871 12871 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12871 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12871

/-! Actual upper energy certificates on all 43 source endpoints at 12871. -/
namespace BstLean.Part269.N12871
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12871)
open BstLean.Part268 (cell12871)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12871 (gMinus 12871) (1 - (cell12871 i).lower) ≤ 1 ∧
    energyUpper 12871 (gMinus 12871) (BstLean.Part211.gPlus 12871)
      (finiteEnergy 12871 12871 0.011) (1 - (cell12871 i).lower) ≤
      (cell12871 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨10,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨11,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨12,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨13,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨14,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨15,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨16,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨17,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨18,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨19,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨20,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨21,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨22,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨23,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨24,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨25,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨26,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨27,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨28,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨29,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨30,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨31,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨32,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨33,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨34,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨35,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨36,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨37,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨38,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨39,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨40,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨41,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨42,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨43,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨44,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨45,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨46,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨47,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨48,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨49,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨50,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨51,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12871) (by norm_num)
        (q := 1 - (cell12871 ⟨52,by decide⟩).lower)
        (by norm_num [cell12871]) (by norm_num [cell12871])
      exact ⟨E.1,E.2.trans (by norm_num [cell12871])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12871

/-! Source-cell containment and simple scalar guards at 12871. -/
namespace BstLean.Part269.N12871
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12871)
open BstLean.Part268 (cell12871)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12871 ⟨10,by decide⟩).lower ∧ (cell12871 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12871 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12871 ⟨11,by decide⟩).lower ∧ (cell12871 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12871 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12871 ⟨12,by decide⟩).lower ∧ (cell12871 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12871 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12871 ⟨13,by decide⟩).lower ∧ (cell12871 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12871 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12871 ⟨14,by decide⟩).lower ∧ (cell12871 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12871 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12871 ⟨15,by decide⟩).lower ∧ (cell12871 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12871 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12871 ⟨16,by decide⟩).lower ∧ (cell12871 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12871 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12871 ⟨17,by decide⟩).lower ∧ (cell12871 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12871 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12871 ⟨18,by decide⟩).lower ∧ (cell12871 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12871 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12871 ⟨19,by decide⟩).lower ∧ (cell12871 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12871 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12871 ⟨20,by decide⟩).lower ∧ (cell12871 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12871 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12871 ⟨21,by decide⟩).lower ∧ (cell12871 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12871 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12871 ⟨22,by decide⟩).lower ∧ (cell12871 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12871 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12871 ⟨23,by decide⟩).lower ∧ (cell12871 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12871 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12871 ⟨24,by decide⟩).lower ∧ (cell12871 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12871 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12871 ⟨25,by decide⟩).lower ∧ (cell12871 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12871 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12871 ⟨26,by decide⟩).lower ∧ (cell12871 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12871 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12871 ⟨27,by decide⟩).lower ∧ (cell12871 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12871 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12871 ⟨28,by decide⟩).lower ∧ (cell12871 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12871 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12871 ⟨29,by decide⟩).lower ∧ (cell12871 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12871 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12871 ⟨30,by decide⟩).lower ∧ (cell12871 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12871 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12871 ⟨31,by decide⟩).lower ∧ (cell12871 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12871 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12871 ⟨32,by decide⟩).lower ∧ (cell12871 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12871 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12871 ⟨33,by decide⟩).lower ∧ (cell12871 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12871 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12871 ⟨34,by decide⟩).lower ∧ (cell12871 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12871 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12871 ⟨35,by decide⟩).lower ∧ (cell12871 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12871 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12871 ⟨36,by decide⟩).lower ∧ (cell12871 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12871 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12871 ⟨37,by decide⟩).lower ∧ (cell12871 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12871 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12871 ⟨38,by decide⟩).lower ∧ (cell12871 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12871 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12871 ⟨39,by decide⟩).lower ∧ (cell12871 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12871 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12871 ⟨40,by decide⟩).lower ∧ (cell12871 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12871 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12871 ⟨41,by decide⟩).lower ∧ (cell12871 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12871 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12871 ⟨42,by decide⟩).lower ∧ (cell12871 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12871 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12871 ⟨43,by decide⟩).lower ∧ (cell12871 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12871 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12871 ⟨44,by decide⟩).lower ∧ (cell12871 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12871 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12871 ⟨45,by decide⟩).lower ∧ (cell12871 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12871 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12871 ⟨46,by decide⟩).lower ∧ (cell12871 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12871 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12871 ⟨47,by decide⟩).lower ∧ (cell12871 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12871 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12871 ⟨48,by decide⟩).lower ∧ (cell12871 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12871 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12871 ⟨49,by decide⟩).lower ∧ (cell12871 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12871 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12871 ⟨50,by decide⟩).lower ∧ (cell12871 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12871 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12871 ⟨51,by decide⟩).lower ∧ (cell12871 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12871 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12871 ⟨52,by decide⟩).lower ∧ (cell12871 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12871 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12871 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12871 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12871,cell12871,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12871 i).lower ∧
    (cell12871 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12871 i).upper ≤ (0.532 : ℝ) ∧
    (cell12871 i).centre ≤ (0.1 : ℝ) ∧ (cell12871 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12871 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12871 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12871

/-! The local source numeric instances at 12871 have no network premises. -/
namespace BstLean.Part269.N12871
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12871)
open BstLean.Part268 (cell12871)

noncomputable def sourceNumerics12871 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12871 (cell12871 i)
      scalarRow12871.M scalarRow12871.H scalarRow12871.xi := by
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
    energy_allowance := scalarRow12871.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12871]
    centre_nonneg := (scalarRow12871.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12871])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12871
/-! Actual 12872 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12872
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12872 ≤ (1.035567071731 : ℝ) := by
  have hr : (113.454836829462 : ℝ) ≤ √(12872 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.454836829462 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12872 12872 (11 / 1000) ≤
    (0.008425264244 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12872) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.454836829462 : ℝ) ≤ √(12872 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12872)
  have hdiv : K / √(12872 : ℝ) ≤ K / 113.454836829462 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.454836829462 ≤ (0.008425264244 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12872.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12872 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12872 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12872 := gPlus_lower 12872
end BstLean.Part269.N12872

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12872
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035567071730 : ℝ) ≤ wn 12872 := by
  have hn : √(12872 : ℝ) ≤ 113.454836829463 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12872 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.454836829463 ≤ 2 / √(12872 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248457055 : ℝ) ≤ rhoBar 12872 BstLean.Part154.csC ∧
    rhoBar 12872 BstLean.Part154.csC ≤ 0.000248457439 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035567071730 : ℝ) / (1.295212 * 12872) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035567071731 : ℝ) / (1.29521 * 12872) := by gcongr
      _ ≤ (0.000248457439 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12872 BstLean.Part154.csC) ≤ 0.000993891488 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12872 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12872 BstLean.Part154.csC) (piBar (rhoBar 12872 BstLean.Part154.csC)) ≤ 0.000189773348 ∧
    cc1 (rhoBar 12872 BstLean.Part154.csC) (piBar (rhoBar 12872 BstLean.Part154.csC)) ≤ 0.000120754066 ∧
    cc2 (rhoBar 12872 BstLean.Part154.csC) ≤ 0.000070098691 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12872 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12872 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12872 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12872 BstLean.Part154.csC * nuR (rhoBar 12872 BstLean.Part154.csC)) ≤ 0.000496930311 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248457439 : ℝ) * 0.000993891488 := by gcongr
      _ ≤ (0.000496930311 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12872 BstLean.Part154.csC) * nuR (rhoBar 12872 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000993891488 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12872 BstLean.Part154.csC) * rhoBar 12872 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248457439 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248457439 / 2 + 0.399 * 0.000993891488 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189773348 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496930311 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120754066 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248457439 / 1.414213562 := by gcongr
      _ ≤ (0.000070098691 : ℝ) := by norm_num

end BstLean.Part269.N12872

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12872
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12872 BstLean.Part154.csC) (piBar (rhoBar 12872 BstLean.Part154.csC)) ≤ 1.55527E-7 := by
  have hr0 : 0 ≤ rhoBar 12872 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12872 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12872 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12872 BstLean.Part154.csC) (piBar (rhoBar 12872 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12872 BstLean.Part154.csC) (piBar (rhoBar 12872 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12872 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189773348 : ℝ) ^ 2 + 0.000120754066 ^ 2 + 3 * 0.000070098691 ^ 2 +
        2 * 0.797885 * 0.000189773348 * 0.000120754066 + 2 * 0.000189773348 * 0.000070098691 +
        4 * 0.797885 * 0.000120754066 * 0.000070098691 := by gcongr
    _ ≤ (1.55527E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12872 BstLean.Part154.csC Θ ≤ 0.002592941303 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12872 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12872 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12872 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12872 BstLean.Part154.csC) (piBar (rhoBar 12872 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12872 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035567071731 * 1.55527E-7 / (0.000248457055 : ℝ) := by gcongr
    _ ≤ 0.002592941303 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12872 BstLean.Part154.csC Θ ≤ 0.002876334876 + 0.000655194800 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12872 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12872 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12872 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035567071731 : ℝ) * ((2 * Θ * 0.000248457439 +
        (6863 / 10000) * 0.000248457439 * 12872 * 0.000993891488) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002876334876 + 0.000655194800 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12872 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12872 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12872 0.011 Θ ∧ gammaRatio 12872 0.011 Θ ≤ 0.000085413243 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12872 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035567071731 : ℝ) * 0.525 / ((1 - 0.011) * 12872) := by gcongr
      _ ≤ (0.000085413243 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12872 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12872 0.011 Θ) :=
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
    badAllowance 12872 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12872 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12872 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12872 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12872 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12872 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12872 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12872 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12872 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12872 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12872 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035567071731 : ℝ) * 12872 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12872 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003359078038 + 0.003248136103 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12872

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12872
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12872 BstLean.Part154.csC) (piBar (rhoBar 12872 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12872 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12872 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12872 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12872 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12872 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12872 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12872 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12872 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12872 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12872 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12872 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12872 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12872 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12872 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052128687431 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12872) ≤ 0.010526105493 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12872 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035567071731)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010526105493 + 2 * 0.737676 / 12872) := by gcongr
    _ ≤ (0.052128687431 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12872 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12872

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12872
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511242705 : ℝ) ≤ plow 12872 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12872) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052570949493)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361294185) : eMP 12872 0.011 xi bn ≤ 0.001172177171 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12872 : ℝ) * (1 - 0.011))) ≤ 0.000579601891 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001361294185 / (12872 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579601891 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579601891 : ℝ) + 3.141593 * 0.052570949493 / (12872 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001172177171 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052570949493)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361294185) : PiBarMP 12872 12 0.011 xi bn ≤ 0.160159214293 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12872 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036895720416 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.829109719079 : ℝ) ≤ √((12872 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.454836829462 : ℝ) ≤ √(12872 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12872) ≤ 0.122801360014 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036895720416 + 0.052570949493 * 1.772454 / (2 * (112.829109719079 : ℝ))) * (1 + 0.001172177171) +
        8 / (12872 * 113.454836829462) + 0.122801360014 := by gcongr
    _ ≤ (0.160159214293 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052570949493)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361294185) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281412244393) :
    parallelOracle 12872 0.011 xi bn cd ≤ 0.161136241473 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12872 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12872 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511242705 : ℝ) ≤ plow 12872 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.454836829462 : ℝ) ≤ √(12872 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281412244393 : ℝ) / (2 * 0.560511242705 * 113.454836829462)) * 0.160159214293 +
        0.281412244393 ^ 2 / (2 * 0.560511242705 * 113.454836829462) := by gcongr
    _ ≤ (0.161136241473 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052570949493) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361294185)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281412244393) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12872 12872 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511242705 : ℝ) ≤ plow 12872 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.454836829462 : ℝ) ≤ √(12872 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12872 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12872 Θ 1.22 ≤ 0.011688355800 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.454836829462 := by gcongr <;> linarith
      _ ≤ (0.011688355800 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12872 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12872 12872 0.011 ≤ 0.008425264244 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12872 12872 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12872 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12872 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12872 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12872 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161136241473 + 0.011688355800 + (0.008425264244 : ℝ) *
        (1 + 2 * (0.281412244393 + 0.011688355800) / (0.560511242705 * 113.454836829462))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12872]

end BstLean.Part269.N12872

/-! The original eight local profiles supply actual 12872 moment certificates. -/
namespace BstLean.Part269.N12872
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12872 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12872 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12872 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052570949493 ∧
    0 ≤ bN 12872 BstLean.Part154.csC (groupTheta g) ∧ bN 12872 BstLean.Part154.csC (groupTheta g) ≤ 0.001361294185 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12872 12872 0.011
      (momentAllowance 12872 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12872 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12872 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12872 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12872 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12872 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229283556962 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12872 0.011
      (momentAllowance 12872 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12872 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12872
/-! The actual computed-centre upper energy formula at 12872. -/
namespace BstLean.Part269.N12872
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12872

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12872
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12872)
open BstLean.Part268 (cell12872)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085003805481
  | 2 => 0.085937951107
  | 3 => 0.086869035870
  | 4 => 0.087798197604
  | 5 => 0.088726821208
  | 6 => 0.089656576435
  | 7 => 0.090589459439
  | 8 => 0.091527838167
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12872 12872 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12872 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12872

/-! Actual upper energy certificates on all 43 source endpoints at 12872. -/
namespace BstLean.Part269.N12872
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12872)
open BstLean.Part268 (cell12872)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12872 (gMinus 12872) (1 - (cell12872 i).lower) ≤ 1 ∧
    energyUpper 12872 (gMinus 12872) (BstLean.Part211.gPlus 12872)
      (finiteEnergy 12872 12872 0.011) (1 - (cell12872 i).lower) ≤
      (cell12872 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨10,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨11,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨12,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨13,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨14,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨15,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨16,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨17,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨18,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨19,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨20,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨21,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨22,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨23,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨24,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨25,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨26,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨27,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨28,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨29,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨30,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨31,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨32,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨33,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨34,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨35,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨36,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨37,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨38,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨39,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨40,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨41,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨42,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨43,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨44,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨45,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨46,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨47,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨48,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨49,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨50,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨51,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12872) (by norm_num)
        (q := 1 - (cell12872 ⟨52,by decide⟩).lower)
        (by norm_num [cell12872]) (by norm_num [cell12872])
      exact ⟨E.1,E.2.trans (by norm_num [cell12872])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12872

/-! Source-cell containment and simple scalar guards at 12872. -/
namespace BstLean.Part269.N12872
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12872)
open BstLean.Part268 (cell12872)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12872 ⟨10,by decide⟩).lower ∧ (cell12872 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12872 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12872 ⟨11,by decide⟩).lower ∧ (cell12872 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12872 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12872 ⟨12,by decide⟩).lower ∧ (cell12872 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12872 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12872 ⟨13,by decide⟩).lower ∧ (cell12872 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12872 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12872 ⟨14,by decide⟩).lower ∧ (cell12872 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12872 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12872 ⟨15,by decide⟩).lower ∧ (cell12872 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12872 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12872 ⟨16,by decide⟩).lower ∧ (cell12872 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12872 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12872 ⟨17,by decide⟩).lower ∧ (cell12872 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12872 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12872 ⟨18,by decide⟩).lower ∧ (cell12872 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12872 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12872 ⟨19,by decide⟩).lower ∧ (cell12872 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12872 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12872 ⟨20,by decide⟩).lower ∧ (cell12872 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12872 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12872 ⟨21,by decide⟩).lower ∧ (cell12872 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12872 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12872 ⟨22,by decide⟩).lower ∧ (cell12872 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12872 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12872 ⟨23,by decide⟩).lower ∧ (cell12872 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12872 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12872 ⟨24,by decide⟩).lower ∧ (cell12872 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12872 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12872 ⟨25,by decide⟩).lower ∧ (cell12872 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12872 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12872 ⟨26,by decide⟩).lower ∧ (cell12872 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12872 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12872 ⟨27,by decide⟩).lower ∧ (cell12872 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12872 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12872 ⟨28,by decide⟩).lower ∧ (cell12872 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12872 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12872 ⟨29,by decide⟩).lower ∧ (cell12872 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12872 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12872 ⟨30,by decide⟩).lower ∧ (cell12872 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12872 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12872 ⟨31,by decide⟩).lower ∧ (cell12872 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12872 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12872 ⟨32,by decide⟩).lower ∧ (cell12872 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12872 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12872 ⟨33,by decide⟩).lower ∧ (cell12872 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12872 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12872 ⟨34,by decide⟩).lower ∧ (cell12872 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12872 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12872 ⟨35,by decide⟩).lower ∧ (cell12872 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12872 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12872 ⟨36,by decide⟩).lower ∧ (cell12872 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12872 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12872 ⟨37,by decide⟩).lower ∧ (cell12872 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12872 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12872 ⟨38,by decide⟩).lower ∧ (cell12872 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12872 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12872 ⟨39,by decide⟩).lower ∧ (cell12872 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12872 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12872 ⟨40,by decide⟩).lower ∧ (cell12872 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12872 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12872 ⟨41,by decide⟩).lower ∧ (cell12872 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12872 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12872 ⟨42,by decide⟩).lower ∧ (cell12872 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12872 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12872 ⟨43,by decide⟩).lower ∧ (cell12872 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12872 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12872 ⟨44,by decide⟩).lower ∧ (cell12872 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12872 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12872 ⟨45,by decide⟩).lower ∧ (cell12872 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12872 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12872 ⟨46,by decide⟩).lower ∧ (cell12872 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12872 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12872 ⟨47,by decide⟩).lower ∧ (cell12872 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12872 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12872 ⟨48,by decide⟩).lower ∧ (cell12872 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12872 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12872 ⟨49,by decide⟩).lower ∧ (cell12872 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12872 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12872 ⟨50,by decide⟩).lower ∧ (cell12872 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12872 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12872 ⟨51,by decide⟩).lower ∧ (cell12872 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12872 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12872 ⟨52,by decide⟩).lower ∧ (cell12872 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12872 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12872 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12872 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12872,cell12872,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12872 i).lower ∧
    (cell12872 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12872 i).upper ≤ (0.532 : ℝ) ∧
    (cell12872 i).centre ≤ (0.1 : ℝ) ∧ (cell12872 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12872 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12872 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12872

/-! The local source numeric instances at 12872 have no network premises. -/
namespace BstLean.Part269.N12872
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12872)
open BstLean.Part268 (cell12872)

noncomputable def sourceNumerics12872 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12872 (cell12872 i)
      scalarRow12872.M scalarRow12872.H scalarRow12872.xi := by
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
    energy_allowance := scalarRow12872.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12872]
    centre_nonneg := (scalarRow12872.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12872])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12872
/-! Actual 12873 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12873
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12873 ≤ (1.035565678175 : ℝ) := by
  have hr : (113.459243783836 : ℝ) ≤ √(12873 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.459243783836 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12873 12873 (11 / 1000) ≤
    (0.008424936989 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12873) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.459243783836 : ℝ) ≤ √(12873 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12873)
  have hdiv : K / √(12873 : ℝ) ≤ K / 113.459243783836 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.459243783836 ≤ (0.008424936989 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12873.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12873 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12873 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12873 := gPlus_lower 12873
end BstLean.Part269.N12873

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12873
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035565678174 : ℝ) ≤ wn 12873 := by
  have hn : √(12873 : ℝ) ≤ 113.459243783837 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12873 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.459243783837 ≤ 2 / √(12873 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248437420 : ℝ) ≤ rhoBar 12873 BstLean.Part154.csC ∧
    rhoBar 12873 BstLean.Part154.csC ≤ 0.000248437804 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035565678174 : ℝ) / (1.295212 * 12873) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035565678175 : ℝ) / (1.29521 * 12873) := by gcongr
      _ ≤ (0.000248437804 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12873 BstLean.Part154.csC) ≤ 0.000993812938 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12873 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12873 BstLean.Part154.csC) (piBar (rhoBar 12873 BstLean.Part154.csC)) ≤ 0.000189758350 ∧
    cc1 (rhoBar 12873 BstLean.Part154.csC) (piBar (rhoBar 12873 BstLean.Part154.csC)) ≤ 0.000120744523 ∧
    cc2 (rhoBar 12873 BstLean.Part154.csC) ≤ 0.000070093151 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12873 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12873 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12873 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12873 BstLean.Part154.csC * nuR (rhoBar 12873 BstLean.Part154.csC)) ≤ 0.000496891039 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248437804 : ℝ) * 0.000993812938 := by gcongr
      _ ≤ (0.000496891039 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12873 BstLean.Part154.csC) * nuR (rhoBar 12873 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000993812938 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12873 BstLean.Part154.csC) * rhoBar 12873 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248437804 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248437804 / 2 + 0.399 * 0.000993812938 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189758350 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496891039 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120744523 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248437804 / 1.414213562 := by gcongr
      _ ≤ (0.000070093151 : ℝ) := by norm_num

end BstLean.Part269.N12873

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12873
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12873 BstLean.Part154.csC) (piBar (rhoBar 12873 BstLean.Part154.csC)) ≤ 1.55503E-7 := by
  have hr0 : 0 ≤ rhoBar 12873 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12873 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12873 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12873 BstLean.Part154.csC) (piBar (rhoBar 12873 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12873 BstLean.Part154.csC) (piBar (rhoBar 12873 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12873 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189758350 : ℝ) ^ 2 + 0.000120744523 ^ 2 + 3 * 0.000070093151 ^ 2 +
        2 * 0.797885 * 0.000189758350 * 0.000120744523 + 2 * 0.000189758350 * 0.000070093151 +
        4 * 0.797885 * 0.000120744523 * 0.000070093151 := by gcongr
    _ ≤ (1.55503E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12873 BstLean.Part154.csC Θ ≤ 0.002592742586 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12873 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12873 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12873 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12873 BstLean.Part154.csC) (piBar (rhoBar 12873 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12873 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035565678175 * 1.55503E-7 / (0.000248437420 : ℝ) := by gcongr
    _ ≤ 0.002592742586 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12873 BstLean.Part154.csC Θ ≤ 0.002876099810 + 0.000655142140 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12873 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12873 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12873 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035565678175 : ℝ) * ((2 * Θ * 0.000248437804 +
        (6863 / 10000) * 0.000248437804 * 12873 * 0.000993812938) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002876099810 + 0.000655142140 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12873 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12873 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12873 0.011 Θ ∧ gammaRatio 12873 0.011 Θ ≤ 0.000085406493 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12873 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035565678175 : ℝ) * 0.525 / ((1 - 0.011) * 12873) := by gcongr
      _ ≤ (0.000085406493 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12873 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12873 0.011 Θ) :=
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
    badAllowance 12873 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12873 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12873 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12873 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12873 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12873 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12873 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12873 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12873 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12873 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12873 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035565678175 : ℝ) * 12873 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12873 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003358842972 + 0.003247884726 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12873

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12873
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12873 BstLean.Part154.csC) (piBar (rhoBar 12873 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12873 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12873 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12873 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12873 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12873 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12873 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12873 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12873 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12873 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12873 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12873 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12873 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12873 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12873 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052126640850 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12873) ≤ 0.010525696640 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12873 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035565678175)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010525696640 + 2 * 0.737676 / 12873) := by gcongr
    _ ≤ (0.052126640850 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12873 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12873

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12873
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511286724 : ℝ) ≤ plow 12873 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12873) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052570582454)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361189858) : eMP 12873 0.011 xi bn ≤ 0.001172086628 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12873 : ℝ) * (1 - 0.011))) ≤ 0.000579557169 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001361189858 / (12873 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579557169 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579557169 : ℝ) + 3.141593 * 0.052570582454 / (12873 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001172086628 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052570582454)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361189858) : PiBarMP 12873 12 0.011 xi bn ≤ 0.160153006021 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12873 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036894306580 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.833492368179 : ℝ) ≤ √((12873 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.459243783836 : ℝ) ≤ √(12873 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12873) ≤ 0.122796590195 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036894306580 + 0.052570582454 * 1.772454 / (2 * (112.833492368179 : ℝ))) * (1 + 0.001172086628) +
        8 / (12873 * 113.459243783836) + 0.122796590195 := by gcongr
    _ ≤ (0.160153006021 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052570582454)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361189858) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281409397407) :
    parallelOracle 12873 0.011 xi bn cd ≤ 0.161129965256 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12873 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12873 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511286724 : ℝ) ≤ plow 12873 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.459243783836 : ℝ) ≤ √(12873 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281409397407 : ℝ) / (2 * 0.560511286724 * 113.459243783836)) * 0.160153006021 +
        0.281409397407 ^ 2 / (2 * 0.560511286724 * 113.459243783836) := by gcongr
    _ ≤ (0.161129965256 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052570582454) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361189858)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281409397407) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12873 12873 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511286724 : ℝ) ≤ plow 12873 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.459243783836 : ℝ) ≤ √(12873 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12873 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12873 Θ 1.22 ≤ 0.011687901804 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.459243783836 := by gcongr <;> linarith
      _ ≤ (0.011687901804 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12873 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12873 12873 0.011 ≤ 0.008424936989 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12873 12873 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12873 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12873 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12873 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12873 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161129965256 + 0.011687901804 + (0.008424936989 : ℝ) *
        (1 + 2 * (0.281409397407 + 0.011687901804) / (0.560511286724 * 113.459243783836))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12873]

end BstLean.Part269.N12873

/-! The original eight local profiles supply actual 12873 moment certificates. -/
namespace BstLean.Part269.N12873
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12873 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12873 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12873 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052570582454 ∧
    0 ≤ bN 12873 BstLean.Part154.csC (groupTheta g) ∧ bN 12873 BstLean.Part154.csC (groupTheta g) ≤ 0.001361189858 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12873 12873 0.011
      (momentAllowance 12873 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12873 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12873 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12873 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12873 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12873 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229282756557 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12873 0.011
      (momentAllowance 12873 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12873 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12873
/-! The actual computed-centre upper energy formula at 12873. -/
namespace BstLean.Part269.N12873
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12873

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12873
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12873)
open BstLean.Part268 (cell12873)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085001060977
  | 2 => 0.085935159903
  | 3 => 0.086866191768
  | 4 => 0.087795292938
  | 5 => 0.088723846579
  | 6 => 0.089653520408
  | 7 => 0.090586308208
  | 8 => 0.091524575180
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12873 12873 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12873 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12873

/-! Actual upper energy certificates on all 43 source endpoints at 12873. -/
namespace BstLean.Part269.N12873
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12873)
open BstLean.Part268 (cell12873)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12873 (gMinus 12873) (1 - (cell12873 i).lower) ≤ 1 ∧
    energyUpper 12873 (gMinus 12873) (BstLean.Part211.gPlus 12873)
      (finiteEnergy 12873 12873 0.011) (1 - (cell12873 i).lower) ≤
      (cell12873 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨10,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨11,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨12,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨13,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨14,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨15,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨16,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨17,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨18,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨19,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨20,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨21,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨22,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨23,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨24,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨25,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨26,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨27,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨28,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨29,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨30,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨31,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨32,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨33,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨34,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨35,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨36,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨37,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨38,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨39,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨40,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨41,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨42,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨43,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨44,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨45,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨46,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨47,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨48,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨49,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨50,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨51,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12873) (by norm_num)
        (q := 1 - (cell12873 ⟨52,by decide⟩).lower)
        (by norm_num [cell12873]) (by norm_num [cell12873])
      exact ⟨E.1,E.2.trans (by norm_num [cell12873])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12873

/-! Source-cell containment and simple scalar guards at 12873. -/
namespace BstLean.Part269.N12873
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12873)
open BstLean.Part268 (cell12873)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12873 ⟨10,by decide⟩).lower ∧ (cell12873 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12873 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12873 ⟨11,by decide⟩).lower ∧ (cell12873 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12873 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12873 ⟨12,by decide⟩).lower ∧ (cell12873 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12873 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12873 ⟨13,by decide⟩).lower ∧ (cell12873 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12873 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12873 ⟨14,by decide⟩).lower ∧ (cell12873 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12873 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12873 ⟨15,by decide⟩).lower ∧ (cell12873 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12873 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12873 ⟨16,by decide⟩).lower ∧ (cell12873 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12873 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12873 ⟨17,by decide⟩).lower ∧ (cell12873 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12873 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12873 ⟨18,by decide⟩).lower ∧ (cell12873 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12873 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12873 ⟨19,by decide⟩).lower ∧ (cell12873 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12873 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12873 ⟨20,by decide⟩).lower ∧ (cell12873 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12873 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12873 ⟨21,by decide⟩).lower ∧ (cell12873 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12873 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12873 ⟨22,by decide⟩).lower ∧ (cell12873 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12873 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12873 ⟨23,by decide⟩).lower ∧ (cell12873 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12873 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12873 ⟨24,by decide⟩).lower ∧ (cell12873 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12873 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12873 ⟨25,by decide⟩).lower ∧ (cell12873 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12873 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12873 ⟨26,by decide⟩).lower ∧ (cell12873 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12873 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12873 ⟨27,by decide⟩).lower ∧ (cell12873 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12873 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12873 ⟨28,by decide⟩).lower ∧ (cell12873 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12873 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12873 ⟨29,by decide⟩).lower ∧ (cell12873 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12873 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12873 ⟨30,by decide⟩).lower ∧ (cell12873 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12873 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12873 ⟨31,by decide⟩).lower ∧ (cell12873 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12873 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12873 ⟨32,by decide⟩).lower ∧ (cell12873 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12873 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12873 ⟨33,by decide⟩).lower ∧ (cell12873 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12873 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12873 ⟨34,by decide⟩).lower ∧ (cell12873 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12873 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12873 ⟨35,by decide⟩).lower ∧ (cell12873 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12873 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12873 ⟨36,by decide⟩).lower ∧ (cell12873 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12873 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12873 ⟨37,by decide⟩).lower ∧ (cell12873 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12873 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12873 ⟨38,by decide⟩).lower ∧ (cell12873 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12873 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12873 ⟨39,by decide⟩).lower ∧ (cell12873 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12873 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12873 ⟨40,by decide⟩).lower ∧ (cell12873 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12873 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12873 ⟨41,by decide⟩).lower ∧ (cell12873 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12873 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12873 ⟨42,by decide⟩).lower ∧ (cell12873 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12873 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12873 ⟨43,by decide⟩).lower ∧ (cell12873 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12873 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12873 ⟨44,by decide⟩).lower ∧ (cell12873 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12873 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12873 ⟨45,by decide⟩).lower ∧ (cell12873 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12873 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12873 ⟨46,by decide⟩).lower ∧ (cell12873 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12873 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12873 ⟨47,by decide⟩).lower ∧ (cell12873 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12873 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12873 ⟨48,by decide⟩).lower ∧ (cell12873 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12873 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12873 ⟨49,by decide⟩).lower ∧ (cell12873 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12873 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12873 ⟨50,by decide⟩).lower ∧ (cell12873 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12873 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12873 ⟨51,by decide⟩).lower ∧ (cell12873 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12873 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12873 ⟨52,by decide⟩).lower ∧ (cell12873 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12873 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12873 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12873 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12873,cell12873,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12873 i).lower ∧
    (cell12873 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12873 i).upper ≤ (0.532 : ℝ) ∧
    (cell12873 i).centre ≤ (0.1 : ℝ) ∧ (cell12873 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12873 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12873 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12873

/-! The local source numeric instances at 12873 have no network premises. -/
namespace BstLean.Part269.N12873
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12873)
open BstLean.Part268 (cell12873)

noncomputable def sourceNumerics12873 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12873 (cell12873 i)
      scalarRow12873.M scalarRow12873.H scalarRow12873.xi := by
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
    energy_allowance := scalarRow12873.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12873]
    centre_nonneg := (scalarRow12873.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12873])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12873
/-! Actual 12874 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12874
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12874 ≤ (1.035564284781 : ℝ) := by
  have hr : (113.463650567042 : ℝ) ≤ √(12874 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.463650567042 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12874 12874 (11 / 1000) ≤
    (0.008424609773 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12874) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.463650567042 : ℝ) ≤ √(12874 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12874)
  have hdiv : K / √(12874 : ℝ) ≤ K / 113.463650567042 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.463650567042 ≤ (0.008424609773 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12874.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12874 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12874 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12874 := gPlus_lower 12874
end BstLean.Part269.N12874

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12874
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035564284780 : ℝ) ≤ wn 12874 := by
  have hn : √(12874 : ℝ) ≤ 113.463650567043 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12874 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.463650567043 ≤ 2 / √(12874 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248417788 : ℝ) ≤ rhoBar 12874 BstLean.Part154.csC ∧
    rhoBar 12874 BstLean.Part154.csC ≤ 0.000248418172 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035564284780 : ℝ) / (1.295212 * 12874) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035564284781 : ℝ) / (1.29521 * 12874) := by gcongr
      _ ≤ (0.000248418172 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12874 BstLean.Part154.csC) ≤ 0.000993734400 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12874 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12874 BstLean.Part154.csC) (piBar (rhoBar 12874 BstLean.Part154.csC)) ≤ 0.000189743354 ∧
    cc1 (rhoBar 12874 BstLean.Part154.csC) (piBar (rhoBar 12874 BstLean.Part154.csC)) ≤ 0.000120734981 ∧
    cc2 (rhoBar 12874 BstLean.Part154.csC) ≤ 0.000070087612 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12874 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12874 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12874 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12874 BstLean.Part154.csC * nuR (rhoBar 12874 BstLean.Part154.csC)) ≤ 0.000496851772 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248418172 : ℝ) * 0.000993734400 := by gcongr
      _ ≤ (0.000496851772 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12874 BstLean.Part154.csC) * nuR (rhoBar 12874 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000993734400 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12874 BstLean.Part154.csC) * rhoBar 12874 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248418172 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248418172 / 2 + 0.399 * 0.000993734400 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189743354 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496851772 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120734981 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248418172 / 1.414213562 := by gcongr
      _ ≤ (0.000070087612 : ℝ) := by norm_num

end BstLean.Part269.N12874

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12874
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12874 BstLean.Part154.csC) (piBar (rhoBar 12874 BstLean.Part154.csC)) ≤ 1.55478E-7 := by
  have hr0 : 0 ≤ rhoBar 12874 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12874 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12874 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12874 BstLean.Part154.csC) (piBar (rhoBar 12874 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12874 BstLean.Part154.csC) (piBar (rhoBar 12874 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12874 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189743354 : ℝ) ^ 2 + 0.000120734981 ^ 2 + 3 * 0.000070087612 ^ 2 +
        2 * 0.797885 * 0.000189743354 * 0.000120734981 + 2 * 0.000189743354 * 0.000070087612 +
        4 * 0.797885 * 0.000120734981 * 0.000070087612 := by gcongr
    _ ≤ (1.55478E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12874 BstLean.Part154.csC Θ ≤ 0.002592527133 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12874 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12874 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12874 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12874 BstLean.Part154.csC) (piBar (rhoBar 12874 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12874 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035564284781 * 1.55478E-7 / (0.000248417788 : ℝ) := by gcongr
    _ ≤ 0.002592527133 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12874 BstLean.Part154.csC Θ ≤ 0.002875864781 + 0.000655089488 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12874 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12874 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12874 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035564284781 : ℝ) * ((2 * Θ * 0.000248418172 +
        (6863 / 10000) * 0.000248418172 * 12874 * 0.000993734400) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002875864781 + 0.000655089488 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12874 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12874 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12874 0.011 Θ ∧ gammaRatio 12874 0.011 Θ ≤ 0.000085399744 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12874 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035564284781 : ℝ) * 0.525 / ((1 - 0.011) * 12874) := by gcongr
      _ ≤ (0.000085399744 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12874 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12874 0.011 Θ) :=
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
    badAllowance 12874 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000482743162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12874 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12874 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12874 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12874 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12874 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12874 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12874 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12874 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12874 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12874 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035564284781 : ℝ) * 12874 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000482743162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12874 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003358607943 + 0.003247616621 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12874

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12874
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12874 BstLean.Part154.csC) (piBar (rhoBar 12874 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12874 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12874 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12874 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12874 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12874 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12874 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12874 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12874 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12874 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12874 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12874 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12874 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12874 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12874 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052124594515 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12874) ≤ 0.010525287836 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12874 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035564284781)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010525287836 + 2 * 0.737676 / 12874) := by gcongr
    _ ≤ (0.052124594515 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12874 12 ≤ 0.0015 := by
  exact BstLean.Part269.S20.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12874

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12874
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511330736 : ℝ) ≤ plow 12874 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12874) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052570206670)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361076745) : eMP 12874 0.011 xi bn ≤ 0.001171992350 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12874 : ℝ) * (1 - 0.011))) ≤ 0.000579510580 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001361076745 / (12874 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579510580 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579510580 : ℝ) + 3.141593 * 0.052570206670 / (12874 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001171992350 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052570206670)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361076745) : PiBarMP 12874 12 0.011 xi bn ≤ 0.160146678831 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12874 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036892773615 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.837874847056 : ℝ) ≤ √((12874 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.463650567042 : ℝ) ≤ √(12874 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12874) ≤ 0.122791820933 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036892773615 + 0.052570206670 * 1.772454 / (2 * (112.837874847056 : ℝ))) * (1 + 0.001171992350) +
        8 / (12874 * 113.463650567042) + 0.122791820933 := by gcongr
    _ ≤ (0.160146678831 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052570206670)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361076745) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281406531593) :
    parallelOracle 12874 0.011 xi bn cd ≤ 0.161123569758 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12874 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12874 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511330736 : ℝ) ≤ plow 12874 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.463650567042 : ℝ) ≤ √(12874 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281406531593 : ℝ) / (2 * 0.560511330736 * 113.463650567042)) * 0.160146678831 +
        0.281406531593 ^ 2 / (2 * 0.560511330736 * 113.463650567042) := by gcongr
    _ ≤ (0.161123569758 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052570206670) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001361076745)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281406531593) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12874 12874 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511330736 : ℝ) ≤ plow 12874 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.463650567042 : ℝ) ≤ √(12874 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12874 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12874 Θ 1.22 ≤ 0.011687447860 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.463650567042 := by gcongr <;> linarith
      _ ≤ (0.011687447860 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12874 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12874 12874 0.011 ≤ 0.008424609773 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12874 12874 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12874 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12874 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12874 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12874 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161123569758 + 0.011687447860 + (0.008424609773 : ℝ) *
        (1 + 2 * (0.281406531593 + 0.011687447860) / (0.560511330736 * 113.463650567042))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12874]

end BstLean.Part269.N12874

/-! The original eight local profiles supply actual 12874 moment certificates. -/
namespace BstLean.Part269.N12874
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12874 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12874 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12874 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052570206670 ∧
    0 ≤ bN 12874 BstLean.Part154.csC (groupTheta g) ∧ bN 12874 BstLean.Part154.csC (groupTheta g) ≤ 0.001361076745 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12874 12874 0.011
      (momentAllowance 12874 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12874 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12874 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12874 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12874 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12874 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229281937078 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12874 0.011
      (momentAllowance 12874 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12874 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12874
/-! The actual computed-centre upper energy formula at 12874. -/
namespace BstLean.Part269.N12874
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12874

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12874
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12874)
open BstLean.Part268 (cell12874)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084998317386
  | 2 => 0.085932369648
  | 3 => 0.086863348659
  | 4 => 0.087792389320
  | 5 => 0.088720873063
  | 6 => 0.089650465574
  | 7 => 0.090583158269
  | 8 => 0.091521313602
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12874 12874 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12874 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003364259073 + 0.003253885827 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S20.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S20.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12874

/-! Actual upper energy certificates on all 43 source endpoints at 12874. -/
namespace BstLean.Part269.N12874
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12874)
open BstLean.Part268 (cell12874)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12874 (gMinus 12874) (1 - (cell12874 i).lower) ≤ 1 ∧
    energyUpper 12874 (gMinus 12874) (BstLean.Part211.gPlus 12874)
      (finiteEnergy 12874 12874 0.011) (1 - (cell12874 i).lower) ≤
      (cell12874 i).energy := by
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
      have E := BstLean.Part269.S20.uniformEnergy10 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨10,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy11 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨11,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy12 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨12,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy13 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨13,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy14 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨14,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy15 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨15,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy16 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨16,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy17 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨17,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy18 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨18,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy19 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨19,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy20 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨20,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy21 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨21,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy22 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨22,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy23 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨23,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy24 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨24,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy25 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨25,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy26 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨26,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy27 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨27,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy28 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨28,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy29 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨29,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy30 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨30,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy31 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨31,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy32 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨32,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy33 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨33,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy34 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨34,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy35 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨35,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy36 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨36,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy37 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨37,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy38 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨38,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy39 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨39,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy40 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨40,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy41 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨41,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy42 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨42,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy43 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨43,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy44 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨44,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy45 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨45,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy46 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨46,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy47 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨47,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy48 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨48,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy49 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨49,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy50 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨50,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy51 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨51,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S20.uniformEnergy52 (n := 12874) (by norm_num)
        (q := 1 - (cell12874 ⟨52,by decide⟩).lower)
        (by norm_num [cell12874]) (by norm_num [cell12874])
      exact ⟨E.1,E.2.trans (by norm_num [cell12874])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12874

/-! Source-cell containment and simple scalar guards at 12874. -/
namespace BstLean.Part269.N12874
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12874)
open BstLean.Part268 (cell12874)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12874 ⟨10,by decide⟩).lower ∧ (cell12874 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12874 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12874 ⟨11,by decide⟩).lower ∧ (cell12874 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12874 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12874 ⟨12,by decide⟩).lower ∧ (cell12874 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12874 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12874 ⟨13,by decide⟩).lower ∧ (cell12874 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12874 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12874 ⟨14,by decide⟩).lower ∧ (cell12874 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12874 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12874 ⟨15,by decide⟩).lower ∧ (cell12874 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12874 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12874 ⟨16,by decide⟩).lower ∧ (cell12874 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12874 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12874 ⟨17,by decide⟩).lower ∧ (cell12874 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12874 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12874 ⟨18,by decide⟩).lower ∧ (cell12874 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12874 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12874 ⟨19,by decide⟩).lower ∧ (cell12874 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12874 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12874 ⟨20,by decide⟩).lower ∧ (cell12874 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12874 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12874 ⟨21,by decide⟩).lower ∧ (cell12874 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12874 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12874 ⟨22,by decide⟩).lower ∧ (cell12874 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12874 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12874 ⟨23,by decide⟩).lower ∧ (cell12874 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12874 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12874 ⟨24,by decide⟩).lower ∧ (cell12874 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12874 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12874 ⟨25,by decide⟩).lower ∧ (cell12874 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12874 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12874 ⟨26,by decide⟩).lower ∧ (cell12874 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12874 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12874 ⟨27,by decide⟩).lower ∧ (cell12874 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12874 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12874 ⟨28,by decide⟩).lower ∧ (cell12874 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12874 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12874 ⟨29,by decide⟩).lower ∧ (cell12874 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12874 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12874 ⟨30,by decide⟩).lower ∧ (cell12874 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12874 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12874 ⟨31,by decide⟩).lower ∧ (cell12874 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12874 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12874 ⟨32,by decide⟩).lower ∧ (cell12874 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12874 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12874 ⟨33,by decide⟩).lower ∧ (cell12874 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12874 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12874 ⟨34,by decide⟩).lower ∧ (cell12874 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12874 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12874 ⟨35,by decide⟩).lower ∧ (cell12874 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12874 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12874 ⟨36,by decide⟩).lower ∧ (cell12874 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12874 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12874 ⟨37,by decide⟩).lower ∧ (cell12874 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12874 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12874 ⟨38,by decide⟩).lower ∧ (cell12874 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12874 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12874 ⟨39,by decide⟩).lower ∧ (cell12874 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12874 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12874 ⟨40,by decide⟩).lower ∧ (cell12874 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12874 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12874 ⟨41,by decide⟩).lower ∧ (cell12874 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12874 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12874 ⟨42,by decide⟩).lower ∧ (cell12874 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12874 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12874 ⟨43,by decide⟩).lower ∧ (cell12874 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12874 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12874 ⟨44,by decide⟩).lower ∧ (cell12874 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12874 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12874 ⟨45,by decide⟩).lower ∧ (cell12874 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12874 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12874 ⟨46,by decide⟩).lower ∧ (cell12874 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12874 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12874 ⟨47,by decide⟩).lower ∧ (cell12874 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12874 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12874 ⟨48,by decide⟩).lower ∧ (cell12874 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12874 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12874 ⟨49,by decide⟩).lower ∧ (cell12874 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12874 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12874 ⟨50,by decide⟩).lower ∧ (cell12874 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12874 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12874 ⟨51,by decide⟩).lower ∧ (cell12874 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12874 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12874 ⟨52,by decide⟩).lower ∧ (cell12874 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12874 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12874 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12874 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12874,cell12874,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12874 i).lower ∧
    (cell12874 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12874 i).upper ≤ (0.532 : ℝ) ∧
    (cell12874 i).centre ≤ (0.1 : ℝ) ∧ (cell12874 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12874 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12874 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12874

/-! The local source numeric instances at 12874 have no network premises. -/
namespace BstLean.Part269.N12874
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12874)
open BstLean.Part268 (cell12874)

noncomputable def sourceNumerics12874 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12874 (cell12874 i)
      scalarRow12874.M scalarRow12874.H scalarRow12874.xi := by
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
    energy_allowance := scalarRow12874.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12874]
    centre_nonneg := (scalarRow12874.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D20.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12874])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12874