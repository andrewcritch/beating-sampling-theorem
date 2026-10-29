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
import BstLean.Part269Direction3
import BstLean.Part269Shared3
import BstLean.Part269Finite
import BstLean.Part269Rows3
import BstLean.Part269Source
/-! Actual 12438 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12438
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12438 ≤ (1.036187741365 : ℝ) := by
  have hr : (111.525781772646 : ℝ) ≤ √(12438 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.525781772646 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12438 12438 (11 / 1000) ≤
    (0.008570996691 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12438) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.525781772646 : ℝ) ≤ √(12438 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12438)
  have hdiv : K / √(12438 : ℝ) ≤ K / 111.525781772646 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.525781772646 ≤ (0.008570996691 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12438.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12438 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12438 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12438 := gPlus_lower 12438
end BstLean.Part269.N12438

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12438
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036187741364 : ℝ) ≤ wn 12438 := by
  have hn : √(12438 : ℝ) ≤ 111.525781772647 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12438 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.525781772647 ≤ 2 / √(12438 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257280593 : ℝ) ≤ rhoBar 12438 BstLean.Part154.csC ∧
    rhoBar 12438 BstLean.Part154.csC ≤ 0.000257280992 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036187741364 : ℝ) / (1.295212 * 12438) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036187741365 : ℝ) / (1.29521 * 12438) := by gcongr
      _ ≤ (0.000257280992 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12438 BstLean.Part154.csC) ≤ 0.001029190162 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12438 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12438 BstLean.Part154.csC) (piBar (rhoBar 12438 BstLean.Part154.csC)) ≤ 0.000196513153 ∧
    cc1 (rhoBar 12438 BstLean.Part154.csC) (piBar (rhoBar 12438 BstLean.Part154.csC)) ≤ 0.000125042584 ∧
    cc2 (rhoBar 12438 BstLean.Part154.csC) ≤ 0.000072588129 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12438 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12438 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12438 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12438 BstLean.Part154.csC * nuR (rhoBar 12438 BstLean.Part154.csC)) ≤ 0.000514578533 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257280992 : ℝ) * 0.001029190162 := by gcongr
      _ ≤ (0.000514578533 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12438 BstLean.Part154.csC) * nuR (rhoBar 12438 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001029190162 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12438 BstLean.Part154.csC) * rhoBar 12438 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257280992 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257280992 / 2 + 0.399 * 0.001029190162 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196513153 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514578533 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125042584 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257280992 / 1.414213562 := by gcongr
      _ ≤ (0.000072588129 : ℝ) := by norm_num

end BstLean.Part269.N12438

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12438
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12438 BstLean.Part154.csC) (piBar (rhoBar 12438 BstLean.Part154.csC)) ≤ 1.66770E-7 := by
  have hr0 : 0 ≤ rhoBar 12438 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12438 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12438 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12438 BstLean.Part154.csC) (piBar (rhoBar 12438 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12438 BstLean.Part154.csC) (piBar (rhoBar 12438 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12438 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196513153 : ℝ) ^ 2 + 0.000125042584 ^ 2 + 3 * 0.000072588129 ^ 2 +
        2 * 0.797885 * 0.000196513153 * 0.000125042584 + 2 * 0.000196513153 * 0.000072588129 +
        4 * 0.797885 * 0.000125042584 * 0.000072588129 := by gcongr
    _ ≤ (1.66770E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12438 BstLean.Part154.csC Θ ≤ 0.002686639169 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12438 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12438 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12438 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12438 BstLean.Part154.csC) (piBar (rhoBar 12438 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12438 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036187741365 * 1.66770E-7 / (0.000257280593 : ℝ) := by gcongr
    _ ≤ 0.002686639169 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12438 BstLean.Part154.csC Θ ≤ 0.002982061105 + 0.000678869593 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12438 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12438 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12438 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036187741365 : ℝ) * ((2 * Θ * 0.000257280992 +
        (6863 / 10000) * 0.000257280992 * 12438 * 0.001029190162) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002982061105 + 0.000678869593 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12438 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12438 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12438 0.011 Θ ∧ gammaRatio 12438 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12438 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036187741365 : ℝ) * 0.525 / ((1 - 0.011) * 12438) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12438 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12438 0.011 Θ) :=
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
    badAllowance 12438 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12438 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12438 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12438 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12438 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12438 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12438 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12438 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12438 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12438 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12438 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036187741365 : ℝ) * 12438 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12438 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004182061105 + 0.003365508762 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12438

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12438
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12438 BstLean.Part154.csC) (piBar (rhoBar 12438 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12438 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12438 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12438 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12438 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12438 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12438 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12438 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12438 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12438 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12438 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12438 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12438 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12438 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12438 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053040234699 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12438) ≤ 0.010708174936 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12438 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036187741365)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010708174936 + 2 * 0.737676 / 12438) := by gcongr
    _ ≤ (0.053040234699 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12438 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12438

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12438
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491470292 : ℝ) ≤ plow 12438 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12438) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053455553206)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410485564) : eMP 12438 0.011 xi bn ≤ 0.001214023991 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12438 : ℝ) * (1 - 0.011))) ≤ 0.000600186001 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001410485564 / (12438 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000600186001 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000600186001 : ℝ) + 3.141593 * 0.053455553206 / (12438 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001214023991 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053455553206)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410485564) : PiBarMP 12438 12 0.011 xi bn ≤ 0.162960894214 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12438 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037556431727 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.910693803618 : ℝ) ≤ √((12438 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.525781772646 : ℝ) ≤ √(12438 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12438) ≤ 0.124925448101 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037556431727 + 0.053455553206 * 1.772454 / (2 * (110.910693803618 : ℝ))) * (1 + 0.001214023991) +
        8 / (12438 * 111.525781772646) + 0.124925448101 := by gcongr
    _ ≤ (0.162960894214 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053455553206)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410485564) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284244804737) :
    parallelOracle 12438 0.011 xi bn cd ≤ 0.163977670914 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12438 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12438 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491470292 : ℝ) ≤ plow 12438 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.525781772646 : ℝ) ≤ √(12438 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284244804737 : ℝ) / (2 * 0.560491470292 * 111.525781772646)) * 0.162960894214 +
        0.284244804737 ^ 2 / (2 * 0.560491470292 * 111.525781772646) := by gcongr
    _ ≤ (0.163977670914 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053455553206) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410485564)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284244804737) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12438 12438 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491470292 : ℝ) ≤ plow 12438 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.525781772646 : ℝ) ≤ √(12438 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12438 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12438 Θ 1.22 ≤ 0.011890528620 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.525781772646 := by gcongr <;> linarith
      _ ≤ (0.011890528620 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12438 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12438 12438 0.011 ≤ 0.008570996691 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12438 12438 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12438 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12438 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12438 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12438 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163977670914 + 0.011890528620 + (0.008570996691 : ℝ) *
        (1 + 2 * (0.284244804737 + 0.011890528620) / (0.560491470292 * 111.525781772646))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12438]

end BstLean.Part269.N12438

/-! The original eight local profiles supply actual 12438 moment certificates. -/
namespace BstLean.Part269.N12438
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12438 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12438 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12438 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053455553206 ∧
    0 ≤ bN 12438 BstLean.Part154.csC (groupTheta g) ∧ bN 12438 BstLean.Part154.csC (groupTheta g) ≤ 0.001410485564 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12438 12438 0.011
      (momentAllowance 12438 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12438 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12438 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12438 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12438 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12438 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231204570038 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12438 0.011
      (momentAllowance 12438 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12438 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12438
/-! The actual computed-centre upper energy formula at 12438. -/
namespace BstLean.Part269.N12438
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12438

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12438
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12438)
open BstLean.Part268 (cell12438)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086295118256
  | 2 => 0.087253621607
  | 3 => 0.088212715002
  | 4 => 0.089174369090
  | 5 => 0.090140947159
  | 6 => 0.091115260750
  | 7 => 0.092100630015
  | 8 => 0.093100948778
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12438 12438 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12438 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004185346396 + 0.003369149079 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S3.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12438

/-! Actual upper energy certificates on all 43 source endpoints at 12438. -/
namespace BstLean.Part269.N12438
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12438)
open BstLean.Part268 (cell12438)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12438 (gMinus 12438) (1 - (cell12438 i).lower) ≤ 1 ∧
    energyUpper 12438 (gMinus 12438) (BstLean.Part211.gPlus 12438)
      (finiteEnergy 12438 12438 0.011) (1 - (cell12438 i).lower) ≤
      (cell12438 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨10,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨11,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨12,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨13,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨14,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨15,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨16,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨17,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨18,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨19,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨20,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨21,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨22,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨23,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨24,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨25,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨26,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨27,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨28,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨29,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨30,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨31,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨32,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨33,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨34,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨35,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨36,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨37,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨38,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨39,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨40,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨41,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨42,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨43,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨44,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨45,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨46,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨47,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨48,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨49,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨50,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨51,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12438) (by norm_num)
        (q := 1 - (cell12438 ⟨52,by decide⟩).lower)
        (by norm_num [cell12438]) (by norm_num [cell12438])
      exact ⟨E.1,E.2.trans (by norm_num [cell12438])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12438

/-! Source-cell containment and simple scalar guards at 12438. -/
namespace BstLean.Part269.N12438
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12438)
open BstLean.Part268 (cell12438)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12438 ⟨10,by decide⟩).lower ∧ (cell12438 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12438 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12438 ⟨11,by decide⟩).lower ∧ (cell12438 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12438 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12438 ⟨12,by decide⟩).lower ∧ (cell12438 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12438 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12438 ⟨13,by decide⟩).lower ∧ (cell12438 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12438 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12438 ⟨14,by decide⟩).lower ∧ (cell12438 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12438 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12438 ⟨15,by decide⟩).lower ∧ (cell12438 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12438 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12438 ⟨16,by decide⟩).lower ∧ (cell12438 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12438 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12438 ⟨17,by decide⟩).lower ∧ (cell12438 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12438 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12438 ⟨18,by decide⟩).lower ∧ (cell12438 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12438 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12438 ⟨19,by decide⟩).lower ∧ (cell12438 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12438 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12438 ⟨20,by decide⟩).lower ∧ (cell12438 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12438 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12438 ⟨21,by decide⟩).lower ∧ (cell12438 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12438 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12438 ⟨22,by decide⟩).lower ∧ (cell12438 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12438 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12438 ⟨23,by decide⟩).lower ∧ (cell12438 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12438 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12438 ⟨24,by decide⟩).lower ∧ (cell12438 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12438 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12438 ⟨25,by decide⟩).lower ∧ (cell12438 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12438 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12438 ⟨26,by decide⟩).lower ∧ (cell12438 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12438 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12438 ⟨27,by decide⟩).lower ∧ (cell12438 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12438 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12438 ⟨28,by decide⟩).lower ∧ (cell12438 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12438 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12438 ⟨29,by decide⟩).lower ∧ (cell12438 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12438 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12438 ⟨30,by decide⟩).lower ∧ (cell12438 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12438 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12438 ⟨31,by decide⟩).lower ∧ (cell12438 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12438 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12438 ⟨32,by decide⟩).lower ∧ (cell12438 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12438 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12438 ⟨33,by decide⟩).lower ∧ (cell12438 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12438 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12438 ⟨34,by decide⟩).lower ∧ (cell12438 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12438 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12438 ⟨35,by decide⟩).lower ∧ (cell12438 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12438 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12438 ⟨36,by decide⟩).lower ∧ (cell12438 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12438 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12438 ⟨37,by decide⟩).lower ∧ (cell12438 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12438 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12438 ⟨38,by decide⟩).lower ∧ (cell12438 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12438 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12438 ⟨39,by decide⟩).lower ∧ (cell12438 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12438 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12438 ⟨40,by decide⟩).lower ∧ (cell12438 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12438 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12438 ⟨41,by decide⟩).lower ∧ (cell12438 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12438 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12438 ⟨42,by decide⟩).lower ∧ (cell12438 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12438 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12438 ⟨43,by decide⟩).lower ∧ (cell12438 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12438 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12438 ⟨44,by decide⟩).lower ∧ (cell12438 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12438 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12438 ⟨45,by decide⟩).lower ∧ (cell12438 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12438 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12438 ⟨46,by decide⟩).lower ∧ (cell12438 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12438 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12438 ⟨47,by decide⟩).lower ∧ (cell12438 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12438 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12438 ⟨48,by decide⟩).lower ∧ (cell12438 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12438 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12438 ⟨49,by decide⟩).lower ∧ (cell12438 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12438 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12438 ⟨50,by decide⟩).lower ∧ (cell12438 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12438 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12438 ⟨51,by decide⟩).lower ∧ (cell12438 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12438 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12438 ⟨52,by decide⟩).lower ∧ (cell12438 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12438 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12438 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12438 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12438,cell12438,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12438 i).lower ∧
    (cell12438 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12438 i).upper ≤ (0.532 : ℝ) ∧
    (cell12438 i).centre ≤ (0.1 : ℝ) ∧ (cell12438 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12438 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12438 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12438

/-! The local source numeric instances at 12438 have no network premises. -/
namespace BstLean.Part269.N12438
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12438)
open BstLean.Part268 (cell12438)

noncomputable def sourceNumerics12438 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12438 (cell12438 i)
      scalarRow12438.M scalarRow12438.H scalarRow12438.xi := by
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
    energy_allowance := scalarRow12438.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12438]
    centre_nonneg := (scalarRow12438.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12438])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12438
/-! Actual 12439 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12439
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12439 ≤ (1.036186273801 : ℝ) := by
  have hr : (111.530264950819 : ℝ) ≤ √(12439 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.530264950819 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12439 12439 (11 / 1000) ≤
    (0.008570652160 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12439) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.530264950819 : ℝ) ≤ √(12439 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12439)
  have hdiv : K / √(12439 : ℝ) ≤ K / 111.530264950819 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.530264950819 ≤ (0.008570652160 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12439.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12439 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12439 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12439 := gPlus_lower 12439
end BstLean.Part269.N12439

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12439
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036186273800 : ℝ) ≤ wn 12439 := by
  have hn : √(12439 : ℝ) ≤ 111.530264950820 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12439 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.530264950820 ≤ 2 / √(12439 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257259546 : ℝ) ≤ rhoBar 12439 BstLean.Part154.csC ∧
    rhoBar 12439 BstLean.Part154.csC ≤ 0.000257259944 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036186273800 : ℝ) / (1.295212 * 12439) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036186273801 : ℝ) / (1.29521 * 12439) := by gcongr
      _ ≤ (0.000257259944 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12439 BstLean.Part154.csC) ≤ 0.001029105959 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12439 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12439 BstLean.Part154.csC) (piBar (rhoBar 12439 BstLean.Part154.csC)) ≤ 0.000196497076 ∧
    cc1 (rhoBar 12439 BstLean.Part154.csC) (piBar (rhoBar 12439 BstLean.Part154.csC)) ≤ 0.000125032354 ∧
    cc2 (rhoBar 12439 BstLean.Part154.csC) ≤ 0.000072582191 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12439 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12439 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12439 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12439 BstLean.Part154.csC * nuR (rhoBar 12439 BstLean.Part154.csC)) ≤ 0.000514536434 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257259944 : ℝ) * 0.001029105959 := by gcongr
      _ ≤ (0.000514536434 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12439 BstLean.Part154.csC) * nuR (rhoBar 12439 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001029105959 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12439 BstLean.Part154.csC) * rhoBar 12439 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257259944 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257259944 / 2 + 0.399 * 0.001029105959 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196497076 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514536434 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125032354 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257259944 / 1.414213562 := by gcongr
      _ ≤ (0.000072582191 : ℝ) := by norm_num

end BstLean.Part269.N12439

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12439
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12439 BstLean.Part154.csC) (piBar (rhoBar 12439 BstLean.Part154.csC)) ≤ 1.66743E-7 := by
  have hr0 : 0 ≤ rhoBar 12439 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12439 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12439 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12439 BstLean.Part154.csC) (piBar (rhoBar 12439 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12439 BstLean.Part154.csC) (piBar (rhoBar 12439 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12439 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196497076 : ℝ) ^ 2 + 0.000125032354 ^ 2 + 3 * 0.000072582191 ^ 2 +
        2 * 0.797885 * 0.000196497076 * 0.000125032354 + 2 * 0.000196497076 * 0.000072582191 +
        4 * 0.797885 * 0.000125032354 * 0.000072582191 := by gcongr
    _ ≤ (1.66743E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12439 BstLean.Part154.csC Θ ≤ 0.002686420163 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12439 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12439 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12439 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12439 BstLean.Part154.csC) (piBar (rhoBar 12439 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12439 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036186273801 * 1.66743E-7 / (0.000257259546 : ℝ) := by gcongr
    _ ≤ 0.002686420163 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12439 BstLean.Part154.csC Θ ≤ 0.002981808679 + 0.000678813093 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12439 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12439 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12439 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036186273801 : ℝ) * ((2 * Θ * 0.000257259944 +
        (6863 / 10000) * 0.000257259944 * 12439 * 0.001029105959) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002981808679 + 0.000678813093 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12439 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12439 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12439 0.011 Θ ∧ gammaRatio 12439 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12439 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036186273801 : ℝ) * 0.525 / ((1 - 0.011) * 12439) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12439 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12439 0.011 Θ) :=
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
    badAllowance 12439 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12439 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12439 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12439 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12439 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12439 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12439 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12439 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12439 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12439 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12439 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036186273801 : ℝ) * 12439 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12439 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004181808679 + 0.003365233256 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12439

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12439
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12439 BstLean.Part154.csC) (piBar (rhoBar 12439 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12439 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12439 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12439 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12439 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12439 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12439 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12439 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12439 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12439 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12439 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12439 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12439 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12439 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12439 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053038079286 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12439) ≤ 0.010707744500 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12439 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036186273801)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010707744500 + 2 * 0.737676 / 12439) := by gcongr
    _ ≤ (0.053038079286 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12439 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12439

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12439
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491517437 : ℝ) ≤ plow 12439 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12439) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053455156139)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410370586) : eMP 12439 0.011 xi bn ≤ 0.001213925616 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12439 : ℝ) * (1 - 0.011))) ≤ 0.000600137413 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001410370586 / (12439 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000600137413 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000600137413 : ℝ) + 3.141593 * 0.053455156139 / (12439 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001213925616 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053455156139)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410370586) : PiBarMP 12439 12 0.011 xi bn ≤ 0.162954315166 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12439 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037554900959 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.915152256127 : ℝ) ≤ √((12439 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.530264950819 : ℝ) ≤ √(12439 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12439) ≤ 0.124920426478 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037554900959 + 0.053455156139 * 1.772454 / (2 * (110.915152256127 : ℝ))) * (1 + 0.001213925616) +
        8 / (12439 * 111.530264950819) + 0.124920426478 := by gcongr
    _ ≤ (0.162954315166 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053455156139)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410370586) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284241790630) :
    parallelOracle 12439 0.011 xi bn cd ≤ 0.163971018318 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12439 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12439 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491517437 : ℝ) ≤ plow 12439 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.530264950819 : ℝ) ≤ √(12439 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284241790630 : ℝ) / (2 * 0.560491517437 * 111.530264950819)) * 0.162954315166 +
        0.284241790630 ^ 2 / (2 * 0.560491517437 * 111.530264950819) := by gcongr
    _ ≤ (0.163971018318 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053455156139) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410370586)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284241790630) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12439 12439 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491517437 : ℝ) ≤ plow 12439 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.530264950819 : ℝ) ≤ √(12439 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12439 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12439 Θ 1.22 ≤ 0.011890050657 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.530264950819 := by gcongr <;> linarith
      _ ≤ (0.011890050657 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12439 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12439 12439 0.011 ≤ 0.008570652160 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12439 12439 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12439 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12439 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12439 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12439 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163971018318 + 0.011890050657 + (0.008570652160 : ℝ) *
        (1 + 2 * (0.284241790630 + 0.011890050657) / (0.560491517437 * 111.530264950819))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12439]

end BstLean.Part269.N12439

/-! The original eight local profiles supply actual 12439 moment certificates. -/
namespace BstLean.Part269.N12439
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12439 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12439 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12439 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053455156139 ∧
    0 ≤ bN 12439 BstLean.Part154.csC (groupTheta g) ∧ bN 12439 BstLean.Part154.csC (groupTheta g) ≤ 0.001410370586 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12439 12439 0.011
      (momentAllowance 12439 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12439 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12439 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12439 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12439 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12439 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231203711344 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12439 0.011
      (momentAllowance 12439 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12439 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12439
/-! The actual computed-centre upper energy formula at 12439. -/
namespace BstLean.Part269.N12439
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12439

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12439
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12439)
open BstLean.Part268 (cell12439)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086291876353
  | 2 => 0.087250312262
  | 3 => 0.088209327153
  | 4 => 0.089170889225
  | 5 => 0.090137358903
  | 6 => 0.091111544402
  | 7 => 0.092096762035
  | 8 => 0.093096901220
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12439 12439 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12439 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004185346396 + 0.003369149079 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S3.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12439

/-! Actual upper energy certificates on all 43 source endpoints at 12439. -/
namespace BstLean.Part269.N12439
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12439)
open BstLean.Part268 (cell12439)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12439 (gMinus 12439) (1 - (cell12439 i).lower) ≤ 1 ∧
    energyUpper 12439 (gMinus 12439) (BstLean.Part211.gPlus 12439)
      (finiteEnergy 12439 12439 0.011) (1 - (cell12439 i).lower) ≤
      (cell12439 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨10,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨11,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨12,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨13,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨14,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨15,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨16,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨17,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨18,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨19,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨20,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨21,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨22,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨23,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨24,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨25,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨26,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨27,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨28,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨29,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨30,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨31,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨32,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨33,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨34,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨35,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨36,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨37,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨38,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨39,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨40,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨41,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨42,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨43,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨44,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨45,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨46,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨47,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨48,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨49,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨50,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨51,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12439) (by norm_num)
        (q := 1 - (cell12439 ⟨52,by decide⟩).lower)
        (by norm_num [cell12439]) (by norm_num [cell12439])
      exact ⟨E.1,E.2.trans (by norm_num [cell12439])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12439

/-! Source-cell containment and simple scalar guards at 12439. -/
namespace BstLean.Part269.N12439
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12439)
open BstLean.Part268 (cell12439)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12439 ⟨10,by decide⟩).lower ∧ (cell12439 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12439 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12439 ⟨11,by decide⟩).lower ∧ (cell12439 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12439 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12439 ⟨12,by decide⟩).lower ∧ (cell12439 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12439 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12439 ⟨13,by decide⟩).lower ∧ (cell12439 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12439 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12439 ⟨14,by decide⟩).lower ∧ (cell12439 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12439 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12439 ⟨15,by decide⟩).lower ∧ (cell12439 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12439 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12439 ⟨16,by decide⟩).lower ∧ (cell12439 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12439 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12439 ⟨17,by decide⟩).lower ∧ (cell12439 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12439 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12439 ⟨18,by decide⟩).lower ∧ (cell12439 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12439 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12439 ⟨19,by decide⟩).lower ∧ (cell12439 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12439 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12439 ⟨20,by decide⟩).lower ∧ (cell12439 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12439 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12439 ⟨21,by decide⟩).lower ∧ (cell12439 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12439 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12439 ⟨22,by decide⟩).lower ∧ (cell12439 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12439 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12439 ⟨23,by decide⟩).lower ∧ (cell12439 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12439 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12439 ⟨24,by decide⟩).lower ∧ (cell12439 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12439 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12439 ⟨25,by decide⟩).lower ∧ (cell12439 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12439 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12439 ⟨26,by decide⟩).lower ∧ (cell12439 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12439 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12439 ⟨27,by decide⟩).lower ∧ (cell12439 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12439 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12439 ⟨28,by decide⟩).lower ∧ (cell12439 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12439 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12439 ⟨29,by decide⟩).lower ∧ (cell12439 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12439 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12439 ⟨30,by decide⟩).lower ∧ (cell12439 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12439 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12439 ⟨31,by decide⟩).lower ∧ (cell12439 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12439 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12439 ⟨32,by decide⟩).lower ∧ (cell12439 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12439 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12439 ⟨33,by decide⟩).lower ∧ (cell12439 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12439 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12439 ⟨34,by decide⟩).lower ∧ (cell12439 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12439 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12439 ⟨35,by decide⟩).lower ∧ (cell12439 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12439 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12439 ⟨36,by decide⟩).lower ∧ (cell12439 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12439 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12439 ⟨37,by decide⟩).lower ∧ (cell12439 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12439 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12439 ⟨38,by decide⟩).lower ∧ (cell12439 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12439 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12439 ⟨39,by decide⟩).lower ∧ (cell12439 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12439 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12439 ⟨40,by decide⟩).lower ∧ (cell12439 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12439 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12439 ⟨41,by decide⟩).lower ∧ (cell12439 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12439 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12439 ⟨42,by decide⟩).lower ∧ (cell12439 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12439 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12439 ⟨43,by decide⟩).lower ∧ (cell12439 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12439 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12439 ⟨44,by decide⟩).lower ∧ (cell12439 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12439 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12439 ⟨45,by decide⟩).lower ∧ (cell12439 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12439 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12439 ⟨46,by decide⟩).lower ∧ (cell12439 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12439 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12439 ⟨47,by decide⟩).lower ∧ (cell12439 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12439 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12439 ⟨48,by decide⟩).lower ∧ (cell12439 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12439 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12439 ⟨49,by decide⟩).lower ∧ (cell12439 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12439 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12439 ⟨50,by decide⟩).lower ∧ (cell12439 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12439 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12439 ⟨51,by decide⟩).lower ∧ (cell12439 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12439 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12439 ⟨52,by decide⟩).lower ∧ (cell12439 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12439 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12439 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12439 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12439,cell12439,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12439 i).lower ∧
    (cell12439 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12439 i).upper ≤ (0.532 : ℝ) ∧
    (cell12439 i).centre ≤ (0.1 : ℝ) ∧ (cell12439 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12439 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12439 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12439

/-! The local source numeric instances at 12439 have no network premises. -/
namespace BstLean.Part269.N12439
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12439)
open BstLean.Part268 (cell12439)

noncomputable def sourceNumerics12439 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12439 (cell12439 i)
      scalarRow12439.M scalarRow12439.H scalarRow12439.xi := by
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
    energy_allowance := scalarRow12439.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12439]
    centre_nonneg := (scalarRow12439.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12439])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12439
/-! Actual 12440 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12440
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12440 ≤ (1.036184806415 : ℝ) := by
  have hr : (111.534747948789 : ℝ) ≤ √(12440 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.534747948789 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12440 12440 (11 / 1000) ≤
    (0.008570307671 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12440) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.534747948789 : ℝ) ≤ √(12440 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12440)
  have hdiv : K / √(12440 : ℝ) ≤ K / 111.534747948789 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.534747948789 ≤ (0.008570307671 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12440.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12440 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12440 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12440 := gPlus_lower 12440
end BstLean.Part269.N12440

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12440
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036184806414 : ℝ) ≤ wn 12440 := by
  have hn : √(12440 : ℝ) ≤ 111.534747948790 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12440 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.534747948790 ≤ 2 / √(12440 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257238501 : ℝ) ≤ rhoBar 12440 BstLean.Part154.csC ∧
    rhoBar 12440 BstLean.Part154.csC ≤ 0.000257238899 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036184806414 : ℝ) / (1.295212 * 12440) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036184806415 : ℝ) / (1.29521 * 12440) := by gcongr
      _ ≤ (0.000257238899 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12440 BstLean.Part154.csC) ≤ 0.001029021768 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12440 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12440 BstLean.Part154.csC) (piBar (rhoBar 12440 BstLean.Part154.csC)) ≤ 0.000196481001 ∧
    cc1 (rhoBar 12440 BstLean.Part154.csC) (piBar (rhoBar 12440 BstLean.Part154.csC)) ≤ 0.000125022125 ∧
    cc2 (rhoBar 12440 BstLean.Part154.csC) ≤ 0.000072576253 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12440 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12440 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12440 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12440 BstLean.Part154.csC * nuR (rhoBar 12440 BstLean.Part154.csC)) ≤ 0.000514494341 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257238899 : ℝ) * 0.001029021768 := by gcongr
      _ ≤ (0.000514494341 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12440 BstLean.Part154.csC) * nuR (rhoBar 12440 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001029021768 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12440 BstLean.Part154.csC) * rhoBar 12440 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257238899 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257238899 / 2 + 0.399 * 0.001029021768 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196481001 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514494341 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125022125 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257238899 / 1.414213562 := by gcongr
      _ ≤ (0.000072576253 : ℝ) := by norm_num

end BstLean.Part269.N12440

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12440
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12440 BstLean.Part154.csC) (piBar (rhoBar 12440 BstLean.Part154.csC)) ≤ 1.66716E-7 := by
  have hr0 : 0 ≤ rhoBar 12440 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12440 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12440 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12440 BstLean.Part154.csC) (piBar (rhoBar 12440 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12440 BstLean.Part154.csC) (piBar (rhoBar 12440 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12440 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196481001 : ℝ) ^ 2 + 0.000125022125 ^ 2 + 3 * 0.000072576253 ^ 2 +
        2 * 0.797885 * 0.000196481001 * 0.000125022125 + 2 * 0.000196481001 * 0.000072576253 +
        4 * 0.797885 * 0.000125022125 * 0.000072576253 := by gcongr
    _ ≤ (1.66716E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12440 BstLean.Part154.csC Θ ≤ 0.002686201102 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12440 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12440 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12440 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12440 BstLean.Part154.csC) (piBar (rhoBar 12440 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12440 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036184806415 * 1.66716E-7 / (0.000257238501 : ℝ) := by gcongr
    _ ≤ 0.002686201102 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12440 BstLean.Part154.csC Θ ≤ 0.002981556285 + 0.000678756602 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12440 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12440 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12440 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036184806415 : ℝ) * ((2 * Θ * 0.000257238899 +
        (6863 / 10000) * 0.000257238899 * 12440 * 0.001029021768) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002981556285 + 0.000678756602 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12440 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12440 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12440 0.011 Θ ∧ gammaRatio 12440 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12440 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036184806415 : ℝ) * 0.525 / ((1 - 0.011) * 12440) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12440 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12440 0.011 Θ) :=
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
    badAllowance 12440 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12440 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12440 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12440 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12440 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12440 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12440 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12440 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12440 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12440 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12440 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036184806415 : ℝ) * 12440 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12440 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004181556285 + 0.003364957704 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12440

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12440
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12440 BstLean.Part154.csC) (piBar (rhoBar 12440 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12440 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12440 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12440 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12440 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12440 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12440 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12440 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12440 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12440 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12440 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12440 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12440 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12440 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12440 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053035924135 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12440) ≤ 0.010707314116 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12440 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036184806415)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010707314116 + 2 * 0.737676 / 12440) := by gcongr
    _ ≤ (0.053035924135 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12440 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12440

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12440
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491564573 : ℝ) ≤ plow 12440 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12440) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053454759080)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410255579) : eMP 12440 0.011 xi bn ≤ 0.001213827237 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12440 : ℝ) * (1 - 0.011))) ≤ 0.000600088823 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001410255579 / (12440 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000600088823 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000600088823 : ℝ) + 3.141593 * 0.053454759080 / (12440 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001213827237 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053454759080)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410255579) : PiBarMP 12440 12 0.011 xi bn ≤ 0.162947736276 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12440 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037553369743 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.919610529428 : ℝ) ≤ √((12440 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.534747948789 : ℝ) ≤ √(12440 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12440) ≤ 0.124915405459 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037553369743 + 0.053454759080 * 1.772454 / (2 * (110.919610529428 : ℝ))) * (1 + 0.001213827237) +
        8 / (12440 * 111.534747948789) + 0.124915405459 := by gcongr
    _ ≤ (0.162947736276 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053454759080)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410255579) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284238776800) :
    parallelOracle 12440 0.011 xi bn cd ≤ 0.163964365889 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12440 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12440 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491564573 : ℝ) ≤ plow 12440 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.534747948789 : ℝ) ≤ √(12440 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284238776800 : ℝ) / (2 * 0.560491564573 * 111.534747948789)) * 0.162947736276 +
        0.284238776800 ^ 2 / (2 * 0.560491564573 * 111.534747948789) := by gcongr
    _ ≤ (0.163964365889 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053454759080) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410255579)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284238776800) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12440 12440 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491564573 : ℝ) ≤ plow 12440 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.534747948789 : ℝ) ≤ √(12440 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12440 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12440 Θ 1.22 ≤ 0.011889572751 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.534747948789 := by gcongr <;> linarith
      _ ≤ (0.011889572751 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12440 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12440 12440 0.011 ≤ 0.008570307671 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12440 12440 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12440 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12440 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12440 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12440 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163964365889 + 0.011889572751 + (0.008570307671 : ℝ) *
        (1 + 2 * (0.284238776800 + 0.011889572751) / (0.560491564573 * 111.534747948789))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12440]

end BstLean.Part269.N12440

/-! The original eight local profiles supply actual 12440 moment certificates. -/
namespace BstLean.Part269.N12440
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12440 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12440 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12440 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053454759080 ∧
    0 ≤ bN 12440 BstLean.Part154.csC (groupTheta g) ∧ bN 12440 BstLean.Part154.csC (groupTheta g) ≤ 0.001410255579 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12440 12440 0.011
      (momentAllowance 12440 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12440 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12440 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12440 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12440 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12440 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231202852665 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12440 0.011
      (momentAllowance 12440 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12440 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12440
/-! The actual computed-centre upper energy formula at 12440. -/
namespace BstLean.Part269.N12440
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12440

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12440
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12440)
open BstLean.Part268 (cell12440)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086288635874
  | 2 => 0.087247004405
  | 3 => 0.088205940869
  | 4 => 0.089167411019
  | 5 => 0.090133772421
  | 6 => 0.091107829969
  | 7 => 0.092092896139
  | 8 => 0.093092855947
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12440 12440 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12440 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004185346396 + 0.003369149079 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S3.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12440

/-! Actual upper energy certificates on all 43 source endpoints at 12440. -/
namespace BstLean.Part269.N12440
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12440)
open BstLean.Part268 (cell12440)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12440 (gMinus 12440) (1 - (cell12440 i).lower) ≤ 1 ∧
    energyUpper 12440 (gMinus 12440) (BstLean.Part211.gPlus 12440)
      (finiteEnergy 12440 12440 0.011) (1 - (cell12440 i).lower) ≤
      (cell12440 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨10,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨11,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨12,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨13,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨14,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨15,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨16,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨17,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨18,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨19,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨20,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨21,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨22,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨23,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨24,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨25,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨26,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨27,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨28,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨29,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨30,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨31,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨32,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨33,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨34,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨35,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨36,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨37,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨38,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨39,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨40,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨41,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨42,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨43,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨44,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨45,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨46,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨47,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨48,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨49,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨50,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨51,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12440) (by norm_num)
        (q := 1 - (cell12440 ⟨52,by decide⟩).lower)
        (by norm_num [cell12440]) (by norm_num [cell12440])
      exact ⟨E.1,E.2.trans (by norm_num [cell12440])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12440

/-! Source-cell containment and simple scalar guards at 12440. -/
namespace BstLean.Part269.N12440
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12440)
open BstLean.Part268 (cell12440)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12440 ⟨10,by decide⟩).lower ∧ (cell12440 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12440 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12440 ⟨11,by decide⟩).lower ∧ (cell12440 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12440 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12440 ⟨12,by decide⟩).lower ∧ (cell12440 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12440 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12440 ⟨13,by decide⟩).lower ∧ (cell12440 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12440 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12440 ⟨14,by decide⟩).lower ∧ (cell12440 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12440 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12440 ⟨15,by decide⟩).lower ∧ (cell12440 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12440 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12440 ⟨16,by decide⟩).lower ∧ (cell12440 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12440 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12440 ⟨17,by decide⟩).lower ∧ (cell12440 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12440 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12440 ⟨18,by decide⟩).lower ∧ (cell12440 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12440 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12440 ⟨19,by decide⟩).lower ∧ (cell12440 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12440 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12440 ⟨20,by decide⟩).lower ∧ (cell12440 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12440 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12440 ⟨21,by decide⟩).lower ∧ (cell12440 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12440 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12440 ⟨22,by decide⟩).lower ∧ (cell12440 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12440 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12440 ⟨23,by decide⟩).lower ∧ (cell12440 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12440 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12440 ⟨24,by decide⟩).lower ∧ (cell12440 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12440 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12440 ⟨25,by decide⟩).lower ∧ (cell12440 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12440 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12440 ⟨26,by decide⟩).lower ∧ (cell12440 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12440 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12440 ⟨27,by decide⟩).lower ∧ (cell12440 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12440 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12440 ⟨28,by decide⟩).lower ∧ (cell12440 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12440 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12440 ⟨29,by decide⟩).lower ∧ (cell12440 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12440 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12440 ⟨30,by decide⟩).lower ∧ (cell12440 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12440 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12440 ⟨31,by decide⟩).lower ∧ (cell12440 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12440 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12440 ⟨32,by decide⟩).lower ∧ (cell12440 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12440 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12440 ⟨33,by decide⟩).lower ∧ (cell12440 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12440 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12440 ⟨34,by decide⟩).lower ∧ (cell12440 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12440 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12440 ⟨35,by decide⟩).lower ∧ (cell12440 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12440 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12440 ⟨36,by decide⟩).lower ∧ (cell12440 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12440 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12440 ⟨37,by decide⟩).lower ∧ (cell12440 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12440 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12440 ⟨38,by decide⟩).lower ∧ (cell12440 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12440 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12440 ⟨39,by decide⟩).lower ∧ (cell12440 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12440 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12440 ⟨40,by decide⟩).lower ∧ (cell12440 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12440 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12440 ⟨41,by decide⟩).lower ∧ (cell12440 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12440 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12440 ⟨42,by decide⟩).lower ∧ (cell12440 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12440 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12440 ⟨43,by decide⟩).lower ∧ (cell12440 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12440 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12440 ⟨44,by decide⟩).lower ∧ (cell12440 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12440 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12440 ⟨45,by decide⟩).lower ∧ (cell12440 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12440 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12440 ⟨46,by decide⟩).lower ∧ (cell12440 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12440 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12440 ⟨47,by decide⟩).lower ∧ (cell12440 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12440 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12440 ⟨48,by decide⟩).lower ∧ (cell12440 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12440 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12440 ⟨49,by decide⟩).lower ∧ (cell12440 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12440 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12440 ⟨50,by decide⟩).lower ∧ (cell12440 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12440 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12440 ⟨51,by decide⟩).lower ∧ (cell12440 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12440 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12440 ⟨52,by decide⟩).lower ∧ (cell12440 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12440 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12440 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12440 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12440,cell12440,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12440 i).lower ∧
    (cell12440 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12440 i).upper ≤ (0.532 : ℝ) ∧
    (cell12440 i).centre ≤ (0.1 : ℝ) ∧ (cell12440 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12440 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12440 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12440

/-! The local source numeric instances at 12440 have no network premises. -/
namespace BstLean.Part269.N12440
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12440)
open BstLean.Part268 (cell12440)

noncomputable def sourceNumerics12440 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12440 (cell12440 i)
      scalarRow12440.M scalarRow12440.H scalarRow12440.xi := by
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
    energy_allowance := scalarRow12440.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12440]
    centre_nonneg := (scalarRow12440.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12440])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12440
/-! Actual 12441 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12441
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12441 ≤ (1.036183339207 : ℝ) := by
  have hr : (111.539230766578 : ℝ) ≤ √(12441 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.539230766578 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12441 12441 (11 / 1000) ≤
    (0.008569963223 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12441) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.539230766578 : ℝ) ≤ √(12441 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12441)
  have hdiv : K / √(12441 : ℝ) ≤ K / 111.539230766578 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.539230766578 ≤ (0.008569963223 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12441.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12441 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12441 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12441 := gPlus_lower 12441
end BstLean.Part269.N12441

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12441
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036183339206 : ℝ) ≤ wn 12441 := by
  have hn : √(12441 : ℝ) ≤ 111.539230766579 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12441 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.539230766579 ≤ 2 / √(12441 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257217460 : ℝ) ≤ rhoBar 12441 BstLean.Part154.csC ∧
    rhoBar 12441 BstLean.Part154.csC ≤ 0.000257217859 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036183339206 : ℝ) / (1.295212 * 12441) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036183339207 : ℝ) / (1.29521 * 12441) := by gcongr
      _ ≤ (0.000257217859 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12441 BstLean.Part154.csC) ≤ 0.001028937598 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12441 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12441 BstLean.Part154.csC) (piBar (rhoBar 12441 BstLean.Part154.csC)) ≤ 0.000196464930 ∧
    cc1 (rhoBar 12441 BstLean.Part154.csC) (piBar (rhoBar 12441 BstLean.Part154.csC)) ≤ 0.000125011899 ∧
    cc2 (rhoBar 12441 BstLean.Part154.csC) ≤ 0.000072570317 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12441 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12441 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12441 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12441 BstLean.Part154.csC * nuR (rhoBar 12441 BstLean.Part154.csC)) ≤ 0.000514452259 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257217859 : ℝ) * 0.001028937598 := by gcongr
      _ ≤ (0.000514452259 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12441 BstLean.Part154.csC) * nuR (rhoBar 12441 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001028937598 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12441 BstLean.Part154.csC) * rhoBar 12441 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257217859 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257217859 / 2 + 0.399 * 0.001028937598 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196464930 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514452259 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125011899 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257217859 / 1.414213562 := by gcongr
      _ ≤ (0.000072570317 : ℝ) := by norm_num

end BstLean.Part269.N12441

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12441
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12441 BstLean.Part154.csC) (piBar (rhoBar 12441 BstLean.Part154.csC)) ≤ 1.66688E-7 := by
  have hr0 : 0 ≤ rhoBar 12441 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12441 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12441 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12441 BstLean.Part154.csC) (piBar (rhoBar 12441 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12441 BstLean.Part154.csC) (piBar (rhoBar 12441 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12441 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196464930 : ℝ) ^ 2 + 0.000125011899 ^ 2 + 3 * 0.000072570317 ^ 2 +
        2 * 0.797885 * 0.000196464930 * 0.000125011899 + 2 * 0.000196464930 * 0.000072570317 +
        4 * 0.797885 * 0.000125011899 * 0.000072570317 := by gcongr
    _ ≤ (1.66688E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12441 BstLean.Part154.csC Θ ≤ 0.002685965851 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12441 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12441 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12441 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12441 BstLean.Part154.csC) (piBar (rhoBar 12441 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12441 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036183339207 * 1.66688E-7 / (0.000257217460 : ℝ) := by gcongr
    _ ≤ 0.002685965851 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12441 BstLean.Part154.csC Θ ≤ 0.002981303973 + 0.000678700125 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12441 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12441 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12441 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036183339207 : ℝ) * ((2 * Θ * 0.000257217859 +
        (6863 / 10000) * 0.000257217859 * 12441 * 0.001028937598) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002981303973 + 0.000678700125 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12441 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12441 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12441 0.011 Θ ∧ gammaRatio 12441 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12441 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036183339207 : ℝ) * 0.525 / ((1 - 0.011) * 12441) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12441 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12441 0.011 Θ) :=
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
    badAllowance 12441 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12441 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12441 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12441 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12441 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12441 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12441 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12441 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12441 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12441 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12441 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036183339207 : ℝ) * 12441 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12441 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004181303973 + 0.003364665976 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12441

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12441
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12441 BstLean.Part154.csC) (piBar (rhoBar 12441 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12441 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12441 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12441 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12441 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12441 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12441 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12441 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12441 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12441 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12441 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12441 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12441 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12441 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12441 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053033769241 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12441) ≤ 0.010706883783 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12441 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036183339207)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010706883783 + 2 * 0.737676 / 12441) := by gcongr
    _ ≤ (0.053033769241 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12441 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12441

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12441
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491611703 : ℝ) ≤ plow 12441 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12441) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053454353611)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410132072) : eMP 12441 0.011 xi bn ≤ 0.001213725246 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12441 : ℝ) * (1 - 0.011))) ≤ 0.000600038428 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001410132072 / (12441 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000600038428 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000600038428 : ℝ) + 3.141593 * 0.053454353611 / (12441 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001213725246 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053454353611)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410132072) : PiBarMP 12441 12 0.011 xi bn ≤ 0.162941044413 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12441 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037551725287 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.924068623540 : ℝ) ≤ √((12441 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.539230766578 : ℝ) ≤ √(12441 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12441) ≤ 0.124910385046 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037551725287 + 0.053454353611 * 1.772454 / (2 * (110.924068623540 : ℝ))) * (1 + 0.001213725246) +
        8 / (12441 * 111.539230766578) + 0.124910385046 := by gcongr
    _ ≤ (0.162941044413 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053454353611)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410132072) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284235745035) :
    parallelOracle 12441 0.011 xi bn cd ≤ 0.163957600134 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12441 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12441 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491611703 : ℝ) ≤ plow 12441 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.539230766578 : ℝ) ≤ √(12441 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284235745035 : ℝ) / (2 * 0.560491611703 * 111.539230766578)) * 0.162941044413 +
        0.284235745035 ^ 2 / (2 * 0.560491611703 * 111.539230766578) := by gcongr
    _ ≤ (0.163957600134 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053454353611) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410132072)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284235745035) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12441 12441 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491611703 : ℝ) ≤ plow 12441 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.539230766578 : ℝ) ≤ √(12441 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12441 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12441 Θ 1.22 ≤ 0.011889094904 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.539230766578 := by gcongr <;> linarith
      _ ≤ (0.011889094904 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12441 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12441 12441 0.011 ≤ 0.008569963223 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12441 12441 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12441 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12441 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12441 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12441 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163957600134 + 0.011889094904 + (0.008569963223 : ℝ) *
        (1 + 2 * (0.284235745035 + 0.011889094904) / (0.560491611703 * 111.539230766578))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12441]

end BstLean.Part269.N12441

/-! The original eight local profiles supply actual 12441 moment certificates. -/
namespace BstLean.Part269.N12441
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12441 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12441 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12441 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053454353611 ∧
    0 ≤ bN 12441 BstLean.Part154.csC (groupTheta g) ∧ bN 12441 BstLean.Part154.csC (groupTheta g) ≤ 0.001410132072 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12441 12441 0.011
      (momentAllowance 12441 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12441 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12441 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12441 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12441 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12441 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231201975794 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12441 0.011
      (momentAllowance 12441 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12441 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12441
/-! The actual computed-centre upper energy formula at 12441. -/
namespace BstLean.Part269.N12441
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12441

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12441
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12441)
open BstLean.Part268 (cell12441)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086285396819
  | 2 => 0.087243698034
  | 3 => 0.088202556147
  | 4 => 0.089163934470
  | 5 => 0.090130187713
  | 6 => 0.091104117448
  | 7 => 0.092089032322
  | 8 => 0.093088812956
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12441 12441 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12441 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004185346396 + 0.003369149079 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S3.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12441

/-! Actual upper energy certificates on all 43 source endpoints at 12441. -/
namespace BstLean.Part269.N12441
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12441)
open BstLean.Part268 (cell12441)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12441 (gMinus 12441) (1 - (cell12441 i).lower) ≤ 1 ∧
    energyUpper 12441 (gMinus 12441) (BstLean.Part211.gPlus 12441)
      (finiteEnergy 12441 12441 0.011) (1 - (cell12441 i).lower) ≤
      (cell12441 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨10,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨11,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨12,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨13,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨14,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨15,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨16,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨17,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨18,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨19,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨20,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨21,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨22,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨23,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨24,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨25,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨26,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨27,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨28,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨29,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨30,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨31,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨32,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨33,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨34,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨35,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨36,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨37,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨38,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨39,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨40,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨41,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨42,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨43,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨44,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨45,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨46,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨47,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨48,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨49,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨50,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨51,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12441) (by norm_num)
        (q := 1 - (cell12441 ⟨52,by decide⟩).lower)
        (by norm_num [cell12441]) (by norm_num [cell12441])
      exact ⟨E.1,E.2.trans (by norm_num [cell12441])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12441

/-! Source-cell containment and simple scalar guards at 12441. -/
namespace BstLean.Part269.N12441
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12441)
open BstLean.Part268 (cell12441)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12441 ⟨10,by decide⟩).lower ∧ (cell12441 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12441 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12441 ⟨11,by decide⟩).lower ∧ (cell12441 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12441 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12441 ⟨12,by decide⟩).lower ∧ (cell12441 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12441 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12441 ⟨13,by decide⟩).lower ∧ (cell12441 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12441 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12441 ⟨14,by decide⟩).lower ∧ (cell12441 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12441 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12441 ⟨15,by decide⟩).lower ∧ (cell12441 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12441 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12441 ⟨16,by decide⟩).lower ∧ (cell12441 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12441 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12441 ⟨17,by decide⟩).lower ∧ (cell12441 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12441 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12441 ⟨18,by decide⟩).lower ∧ (cell12441 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12441 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12441 ⟨19,by decide⟩).lower ∧ (cell12441 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12441 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12441 ⟨20,by decide⟩).lower ∧ (cell12441 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12441 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12441 ⟨21,by decide⟩).lower ∧ (cell12441 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12441 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12441 ⟨22,by decide⟩).lower ∧ (cell12441 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12441 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12441 ⟨23,by decide⟩).lower ∧ (cell12441 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12441 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12441 ⟨24,by decide⟩).lower ∧ (cell12441 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12441 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12441 ⟨25,by decide⟩).lower ∧ (cell12441 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12441 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12441 ⟨26,by decide⟩).lower ∧ (cell12441 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12441 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12441 ⟨27,by decide⟩).lower ∧ (cell12441 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12441 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12441 ⟨28,by decide⟩).lower ∧ (cell12441 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12441 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12441 ⟨29,by decide⟩).lower ∧ (cell12441 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12441 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12441 ⟨30,by decide⟩).lower ∧ (cell12441 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12441 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12441 ⟨31,by decide⟩).lower ∧ (cell12441 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12441 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12441 ⟨32,by decide⟩).lower ∧ (cell12441 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12441 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12441 ⟨33,by decide⟩).lower ∧ (cell12441 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12441 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12441 ⟨34,by decide⟩).lower ∧ (cell12441 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12441 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12441 ⟨35,by decide⟩).lower ∧ (cell12441 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12441 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12441 ⟨36,by decide⟩).lower ∧ (cell12441 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12441 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12441 ⟨37,by decide⟩).lower ∧ (cell12441 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12441 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12441 ⟨38,by decide⟩).lower ∧ (cell12441 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12441 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12441 ⟨39,by decide⟩).lower ∧ (cell12441 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12441 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12441 ⟨40,by decide⟩).lower ∧ (cell12441 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12441 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12441 ⟨41,by decide⟩).lower ∧ (cell12441 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12441 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12441 ⟨42,by decide⟩).lower ∧ (cell12441 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12441 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12441 ⟨43,by decide⟩).lower ∧ (cell12441 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12441 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12441 ⟨44,by decide⟩).lower ∧ (cell12441 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12441 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12441 ⟨45,by decide⟩).lower ∧ (cell12441 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12441 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12441 ⟨46,by decide⟩).lower ∧ (cell12441 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12441 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12441 ⟨47,by decide⟩).lower ∧ (cell12441 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12441 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12441 ⟨48,by decide⟩).lower ∧ (cell12441 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12441 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12441 ⟨49,by decide⟩).lower ∧ (cell12441 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12441 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12441 ⟨50,by decide⟩).lower ∧ (cell12441 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12441 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12441 ⟨51,by decide⟩).lower ∧ (cell12441 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12441 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12441 ⟨52,by decide⟩).lower ∧ (cell12441 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12441 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12441 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12441 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12441,cell12441,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12441 i).lower ∧
    (cell12441 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12441 i).upper ≤ (0.532 : ℝ) ∧
    (cell12441 i).centre ≤ (0.1 : ℝ) ∧ (cell12441 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12441 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12441 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12441

/-! The local source numeric instances at 12441 have no network premises. -/
namespace BstLean.Part269.N12441
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12441)
open BstLean.Part268 (cell12441)

noncomputable def sourceNumerics12441 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12441 (cell12441 i)
      scalarRow12441.M scalarRow12441.H scalarRow12441.xi := by
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
    energy_allowance := scalarRow12441.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12441]
    centre_nonneg := (scalarRow12441.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12441])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12441
/-! Actual 12442 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12442
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12442 ≤ (1.036181872177 : ℝ) := by
  have hr : (111.543713404207 : ℝ) ≤ √(12442 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.543713404207 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12442 12442 (11 / 1000) ≤
    (0.008569618817 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12442) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.543713404207 : ℝ) ≤ √(12442 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12442)
  have hdiv : K / √(12442 : ℝ) ≤ K / 111.543713404207 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.543713404207 ≤ (0.008569618817 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12442.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12442 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12442 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12442 := gPlus_lower 12442
end BstLean.Part269.N12442

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12442
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036181872176 : ℝ) ≤ wn 12442 := by
  have hn : √(12442 : ℝ) ≤ 111.543713404208 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12442 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.543713404208 ≤ 2 / √(12442 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257196423 : ℝ) ≤ rhoBar 12442 BstLean.Part154.csC ∧
    rhoBar 12442 BstLean.Part154.csC ≤ 0.000257196821 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036181872176 : ℝ) / (1.295212 * 12442) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036181872177 : ℝ) / (1.29521 * 12442) := by gcongr
      _ ≤ (0.000257196821 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12442 BstLean.Part154.csC) ≤ 0.001028853435 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12442 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12442 BstLean.Part154.csC) (piBar (rhoBar 12442 BstLean.Part154.csC)) ≤ 0.000196448860 ∧
    cc1 (rhoBar 12442 BstLean.Part154.csC) (piBar (rhoBar 12442 BstLean.Part154.csC)) ≤ 0.000125001674 ∧
    cc2 (rhoBar 12442 BstLean.Part154.csC) ≤ 0.000072564381 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12442 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12442 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12442 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12442 BstLean.Part154.csC * nuR (rhoBar 12442 BstLean.Part154.csC)) ≤ 0.000514410180 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257196821 : ℝ) * 0.001028853435 := by gcongr
      _ ≤ (0.000514410180 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12442 BstLean.Part154.csC) * nuR (rhoBar 12442 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001028853435 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12442 BstLean.Part154.csC) * rhoBar 12442 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257196821 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257196821 / 2 + 0.399 * 0.001028853435 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196448860 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514410180 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125001674 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257196821 / 1.414213562 := by gcongr
      _ ≤ (0.000072564381 : ℝ) := by norm_num

end BstLean.Part269.N12442

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12442
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12442 BstLean.Part154.csC) (piBar (rhoBar 12442 BstLean.Part154.csC)) ≤ 1.66661E-7 := by
  have hr0 : 0 ≤ rhoBar 12442 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12442 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12442 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12442 BstLean.Part154.csC) (piBar (rhoBar 12442 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12442 BstLean.Part154.csC) (piBar (rhoBar 12442 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12442 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196448860 : ℝ) ^ 2 + 0.000125001674 ^ 2 + 3 * 0.000072564381 ^ 2 +
        2 * 0.797885 * 0.000196448860 * 0.000125001674 + 2 * 0.000196448860 * 0.000072564381 +
        4 * 0.797885 * 0.000125001674 * 0.000072564381 := by gcongr
    _ ≤ (1.66661E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12442 BstLean.Part154.csC Θ ≤ 0.002685746637 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12442 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12442 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12442 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12442 BstLean.Part154.csC) (piBar (rhoBar 12442 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12442 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036181872177 * 1.66661E-7 / (0.000257196423 : ℝ) := by gcongr
    _ ≤ 0.002685746637 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12442 BstLean.Part154.csC Θ ≤ 0.002981051667 + 0.000678643653 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12442 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12442 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12442 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036181872177 : ℝ) * ((2 * Θ * 0.000257196821 +
        (6863 / 10000) * 0.000257196821 * 12442 * 0.001028853435) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002981051667 + 0.000678643653 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12442 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12442 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12442 0.011 Θ ∧ gammaRatio 12442 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12442 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036181872177 : ℝ) * 0.525 / ((1 - 0.011) * 12442) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12442 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12442 0.011 Θ) :=
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
    badAllowance 12442 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12442 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12442 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12442 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12442 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12442 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12442 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12442 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12442 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12442 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12442 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036181872177 : ℝ) * 12442 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12442 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004181051667 + 0.003364390290 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12442

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12442
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12442 BstLean.Part154.csC) (piBar (rhoBar 12442 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12442 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12442 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12442 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12442 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12442 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12442 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12442 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12442 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12442 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12442 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12442 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12442 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12442 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12442 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053031614614 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12442) ≤ 0.010706453503 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12442 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036181872177)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010706453503 + 2 * 0.737676 / 12442) := by gcongr
    _ ≤ (0.053031614614 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12442 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12442

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12442
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491658824 : ℝ) ≤ plow 12442 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12442) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053453956570)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410016985) : eMP 12442 0.011 xi bn ≤ 0.001213626850 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12442 : ℝ) * (1 - 0.011))) ≤ 0.000599989829 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001410016985 / (12442 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599989829 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599989829 : ℝ) + 3.141593 * 0.053453956570 / (12442 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001213626850 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053453956570)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410016985) : PiBarMP 12442 12 0.011 xi bn ≤ 0.162934465543 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12442 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037550192876 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.928526538487 : ℝ) ≤ √((12442 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.543713404207 : ℝ) ≤ √(12442 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12442) ≤ 0.124905365238 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037550192876 + 0.053453956570 * 1.772454 / (2 * (110.928526538487 : ℝ))) * (1 + 0.001213626850) +
        8 / (12442 * 111.543713404207) + 0.124905365238 := by gcongr
    _ ≤ (0.162934465543 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053453956570)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410016985) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284232731761) :
    parallelOracle 12442 0.011 xi bn cd ≤ 0.163950947745 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12442 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12442 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491658824 : ℝ) ≤ plow 12442 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.543713404207 : ℝ) ≤ √(12442 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284232731761 : ℝ) / (2 * 0.560491658824 * 111.543713404207)) * 0.162934465543 +
        0.284232731761 ^ 2 / (2 * 0.560491658824 * 111.543713404207) := by gcongr
    _ ≤ (0.163950947745 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053453956570) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410016985)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284232731761) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12442 12442 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491658824 : ℝ) ≤ plow 12442 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.543713404207 : ℝ) ≤ √(12442 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12442 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12442 Θ 1.22 ≤ 0.011888617113 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.543713404207 := by gcongr <;> linarith
      _ ≤ (0.011888617113 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12442 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12442 12442 0.011 ≤ 0.008569618817 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12442 12442 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12442 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12442 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12442 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12442 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163950947745 + 0.011888617113 + (0.008569618817 : ℝ) *
        (1 + 2 * (0.284232731761 + 0.011888617113) / (0.560491658824 * 111.543713404207))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12442]

end BstLean.Part269.N12442

/-! The original eight local profiles supply actual 12442 moment certificates. -/
namespace BstLean.Part269.N12442
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12442 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12442 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12442 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053453956570 ∧
    0 ≤ bN 12442 BstLean.Part154.csC (groupTheta g) ∧ bN 12442 BstLean.Part154.csC (groupTheta g) ≤ 0.001410016985 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12442 12442 0.011
      (momentAllowance 12442 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12442 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12442 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12442 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12442 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12442 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231201117147 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12442 0.011
      (momentAllowance 12442 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12442 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12442
/-! The actual computed-centre upper energy formula at 12442. -/
namespace BstLean.Part269.N12442
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12442

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12442
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12442)
open BstLean.Part268 (cell12442)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086282159186
  | 2 => 0.087240393146
  | 3 => 0.088199172986
  | 4 => 0.089160459577
  | 5 => 0.090126604774
  | 6 => 0.091100406838
  | 7 => 0.092085170584
  | 8 => 0.093084772244
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12442 12442 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12442 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004185346396 + 0.003369149079 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S3.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12442

/-! Actual upper energy certificates on all 43 source endpoints at 12442. -/
namespace BstLean.Part269.N12442
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12442)
open BstLean.Part268 (cell12442)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12442 (gMinus 12442) (1 - (cell12442 i).lower) ≤ 1 ∧
    energyUpper 12442 (gMinus 12442) (BstLean.Part211.gPlus 12442)
      (finiteEnergy 12442 12442 0.011) (1 - (cell12442 i).lower) ≤
      (cell12442 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨10,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨11,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨12,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨13,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨14,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨15,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨16,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨17,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨18,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨19,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨20,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨21,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨22,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨23,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨24,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨25,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨26,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨27,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨28,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨29,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨30,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨31,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨32,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨33,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨34,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨35,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨36,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨37,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨38,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨39,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨40,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨41,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨42,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨43,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨44,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨45,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨46,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨47,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨48,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨49,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨50,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨51,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12442) (by norm_num)
        (q := 1 - (cell12442 ⟨52,by decide⟩).lower)
        (by norm_num [cell12442]) (by norm_num [cell12442])
      exact ⟨E.1,E.2.trans (by norm_num [cell12442])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12442

/-! Source-cell containment and simple scalar guards at 12442. -/
namespace BstLean.Part269.N12442
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12442)
open BstLean.Part268 (cell12442)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12442 ⟨10,by decide⟩).lower ∧ (cell12442 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12442 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12442 ⟨11,by decide⟩).lower ∧ (cell12442 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12442 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12442 ⟨12,by decide⟩).lower ∧ (cell12442 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12442 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12442 ⟨13,by decide⟩).lower ∧ (cell12442 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12442 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12442 ⟨14,by decide⟩).lower ∧ (cell12442 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12442 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12442 ⟨15,by decide⟩).lower ∧ (cell12442 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12442 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12442 ⟨16,by decide⟩).lower ∧ (cell12442 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12442 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12442 ⟨17,by decide⟩).lower ∧ (cell12442 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12442 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12442 ⟨18,by decide⟩).lower ∧ (cell12442 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12442 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12442 ⟨19,by decide⟩).lower ∧ (cell12442 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12442 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12442 ⟨20,by decide⟩).lower ∧ (cell12442 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12442 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12442 ⟨21,by decide⟩).lower ∧ (cell12442 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12442 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12442 ⟨22,by decide⟩).lower ∧ (cell12442 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12442 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12442 ⟨23,by decide⟩).lower ∧ (cell12442 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12442 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12442 ⟨24,by decide⟩).lower ∧ (cell12442 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12442 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12442 ⟨25,by decide⟩).lower ∧ (cell12442 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12442 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12442 ⟨26,by decide⟩).lower ∧ (cell12442 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12442 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12442 ⟨27,by decide⟩).lower ∧ (cell12442 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12442 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12442 ⟨28,by decide⟩).lower ∧ (cell12442 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12442 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12442 ⟨29,by decide⟩).lower ∧ (cell12442 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12442 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12442 ⟨30,by decide⟩).lower ∧ (cell12442 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12442 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12442 ⟨31,by decide⟩).lower ∧ (cell12442 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12442 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12442 ⟨32,by decide⟩).lower ∧ (cell12442 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12442 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12442 ⟨33,by decide⟩).lower ∧ (cell12442 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12442 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12442 ⟨34,by decide⟩).lower ∧ (cell12442 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12442 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12442 ⟨35,by decide⟩).lower ∧ (cell12442 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12442 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12442 ⟨36,by decide⟩).lower ∧ (cell12442 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12442 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12442 ⟨37,by decide⟩).lower ∧ (cell12442 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12442 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12442 ⟨38,by decide⟩).lower ∧ (cell12442 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12442 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12442 ⟨39,by decide⟩).lower ∧ (cell12442 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12442 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12442 ⟨40,by decide⟩).lower ∧ (cell12442 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12442 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12442 ⟨41,by decide⟩).lower ∧ (cell12442 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12442 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12442 ⟨42,by decide⟩).lower ∧ (cell12442 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12442 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12442 ⟨43,by decide⟩).lower ∧ (cell12442 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12442 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12442 ⟨44,by decide⟩).lower ∧ (cell12442 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12442 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12442 ⟨45,by decide⟩).lower ∧ (cell12442 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12442 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12442 ⟨46,by decide⟩).lower ∧ (cell12442 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12442 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12442 ⟨47,by decide⟩).lower ∧ (cell12442 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12442 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12442 ⟨48,by decide⟩).lower ∧ (cell12442 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12442 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12442 ⟨49,by decide⟩).lower ∧ (cell12442 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12442 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12442 ⟨50,by decide⟩).lower ∧ (cell12442 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12442 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12442 ⟨51,by decide⟩).lower ∧ (cell12442 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12442 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12442 ⟨52,by decide⟩).lower ∧ (cell12442 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12442 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12442 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12442 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12442,cell12442,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12442 i).lower ∧
    (cell12442 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12442 i).upper ≤ (0.532 : ℝ) ∧
    (cell12442 i).centre ≤ (0.1 : ℝ) ∧ (cell12442 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12442 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12442 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12442

/-! The local source numeric instances at 12442 have no network premises. -/
namespace BstLean.Part269.N12442
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12442)
open BstLean.Part268 (cell12442)

noncomputable def sourceNumerics12442 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12442 (cell12442 i)
      scalarRow12442.M scalarRow12442.H scalarRow12442.xi := by
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
    energy_allowance := scalarRow12442.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12442]
    centre_nonneg := (scalarRow12442.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12442])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12442
/-! Actual 12443 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12443
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12443 ≤ (1.036180405325 : ℝ) := by
  have hr : (111.548195861699 : ℝ) ≤ √(12443 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.548195861699 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12443 12443 (11 / 1000) ≤
    (0.008569274453 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12443) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.548195861699 : ℝ) ≤ √(12443 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12443)
  have hdiv : K / √(12443 : ℝ) ≤ K / 111.548195861699 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.548195861699 ≤ (0.008569274453 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12443.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12443 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12443 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12443 := gPlus_lower 12443
end BstLean.Part269.N12443

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12443
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036180405324 : ℝ) ≤ wn 12443 := by
  have hn : √(12443 : ℝ) ≤ 111.548195861700 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12443 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.548195861700 ≤ 2 / √(12443 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257175389 : ℝ) ≤ rhoBar 12443 BstLean.Part154.csC ∧
    rhoBar 12443 BstLean.Part154.csC ≤ 0.000257175787 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036180405324 : ℝ) / (1.295212 * 12443) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036180405325 : ℝ) / (1.29521 * 12443) := by gcongr
      _ ≤ (0.000257175787 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12443 BstLean.Part154.csC) ≤ 0.001028769288 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12443 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12443 BstLean.Part154.csC) (piBar (rhoBar 12443 BstLean.Part154.csC)) ≤ 0.000196432793 ∧
    cc1 (rhoBar 12443 BstLean.Part154.csC) (piBar (rhoBar 12443 BstLean.Part154.csC)) ≤ 0.000124991451 ∧
    cc2 (rhoBar 12443 BstLean.Part154.csC) ≤ 0.000072558447 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12443 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12443 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12443 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12443 BstLean.Part154.csC * nuR (rhoBar 12443 BstLean.Part154.csC)) ≤ 0.000514368109 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257175787 : ℝ) * 0.001028769288 := by gcongr
      _ ≤ (0.000514368109 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12443 BstLean.Part154.csC) * nuR (rhoBar 12443 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001028769288 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12443 BstLean.Part154.csC) * rhoBar 12443 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257175787 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257175787 / 2 + 0.399 * 0.001028769288 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196432793 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514368109 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124991451 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257175787 / 1.414213562 := by gcongr
      _ ≤ (0.000072558447 : ℝ) := by norm_num

end BstLean.Part269.N12443

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12443
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12443 BstLean.Part154.csC) (piBar (rhoBar 12443 BstLean.Part154.csC)) ≤ 1.66634E-7 := by
  have hr0 : 0 ≤ rhoBar 12443 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12443 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12443 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12443 BstLean.Part154.csC) (piBar (rhoBar 12443 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12443 BstLean.Part154.csC) (piBar (rhoBar 12443 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12443 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196432793 : ℝ) ^ 2 + 0.000124991451 ^ 2 + 3 * 0.000072558447 ^ 2 +
        2 * 0.797885 * 0.000196432793 * 0.000124991451 + 2 * 0.000196432793 * 0.000072558447 +
        4 * 0.797885 * 0.000124991451 * 0.000072558447 := by gcongr
    _ ≤ (1.66634E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12443 BstLean.Part154.csC Θ ≤ 0.002685527357 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12443 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12443 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12443 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12443 BstLean.Part154.csC) (piBar (rhoBar 12443 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12443 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036180405325 * 1.66634E-7 / (0.000257175389 : ℝ) := by gcongr
    _ ≤ 0.002685527357 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12443 BstLean.Part154.csC Θ ≤ 0.002980799417 + 0.000678587191 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12443 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12443 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12443 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036180405325 : ℝ) * ((2 * Θ * 0.000257175787 +
        (6863 / 10000) * 0.000257175787 * 12443 * 0.001028769288) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002980799417 + 0.000678587191 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12443 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12443 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12443 0.011 Θ ∧ gammaRatio 12443 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12443 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036180405325 : ℝ) * 0.525 / ((1 - 0.011) * 12443) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12443 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12443 0.011 Θ) :=
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
    badAllowance 12443 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12443 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12443 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12443 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12443 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12443 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12443 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12443 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12443 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12443 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12443 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036180405325 : ℝ) * 12443 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12443 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004180799417 + 0.003364114548 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12443

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12443
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12443 BstLean.Part154.csC) (piBar (rhoBar 12443 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12443 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12443 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12443 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12443 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12443 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12443 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12443 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12443 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12443 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12443 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12443 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12443 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12443 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12443 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053029460245 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12443) ≤ 0.010706023274 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12443 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036180405325)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010706023274 + 2 * 0.737676 / 12443) := by gcongr
    _ ≤ (0.053029460245 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12443 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12443

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12443
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491705939 : ℝ) ≤ plow 12443 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12443) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053453559555)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409901863) : eMP 12443 0.011 xi bn ≤ 0.001213528446 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12443 : ℝ) * (1 - 0.011))) ≤ 0.000599941226 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001409901863 / (12443 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599941226 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599941226 : ℝ) + 3.141593 * 0.053453559555 / (12443 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001213528446 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053453559555)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409901863) : PiBarMP 12443 12 0.011 xi bn ≤ 0.162927886752 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12443 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037548659937 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.932984274290 : ℝ) ≤ √((12443 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.548195861699 : ℝ) ≤ √(12443 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12443) ≤ 0.124900346036 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037548659937 + 0.053453559555 * 1.772454 / (2 * (110.932984274290 : ℝ))) * (1 + 0.001213528446) +
        8 / (12443 * 111.548195861699) + 0.124900346036 := by gcongr
    _ ≤ (0.162927886752 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053453559555)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409901863) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284229718799) :
    parallelOracle 12443 0.011 xi bn cd ≤ 0.163944295445 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12443 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12443 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491705939 : ℝ) ≤ plow 12443 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.548195861699 : ℝ) ≤ √(12443 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284229718799 : ℝ) / (2 * 0.560491705939 * 111.548195861699)) * 0.162927886752 +
        0.284229718799 ^ 2 / (2 * 0.560491705939 * 111.548195861699) := by gcongr
    _ ≤ (0.163944295445 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053453559555) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409901863)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284229718799) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12443 12443 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491705939 : ℝ) ≤ plow 12443 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.548195861699 : ℝ) ≤ √(12443 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12443 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12443 Θ 1.22 ≤ 0.011888139381 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.548195861699 := by gcongr <;> linarith
      _ ≤ (0.011888139381 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12443 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12443 12443 0.011 ≤ 0.008569274453 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12443 12443 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12443 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12443 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12443 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12443 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163944295445 + 0.011888139381 + (0.008569274453 : ℝ) *
        (1 + 2 * (0.284229718799 + 0.011888139381) / (0.560491705939 * 111.548195861699))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12443]

end BstLean.Part269.N12443

/-! The original eight local profiles supply actual 12443 moment certificates. -/
namespace BstLean.Part269.N12443
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12443 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12443 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12443 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053453559555 ∧
    0 ≤ bN 12443 BstLean.Part154.csC (groupTheta g) ∧ bN 12443 BstLean.Part154.csC (groupTheta g) ≤ 0.001409901863 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12443 12443 0.011
      (momentAllowance 12443 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12443 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12443 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12443 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12443 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12443 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231200258554 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12443 0.011
      (momentAllowance 12443 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12443 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12443
/-! The actual computed-centre upper energy formula at 12443. -/
namespace BstLean.Part269.N12443
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12443

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12443
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12443)
open BstLean.Part268 (cell12443)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086278922973
  | 2 => 0.087237089742
  | 3 => 0.088195791385
  | 4 => 0.089156986338
  | 5 => 0.090123023605
  | 6 => 0.091096698135
  | 7 => 0.092081310922
  | 8 => 0.093080733809
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12443 12443 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12443 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004185346396 + 0.003369149079 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S3.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12443

/-! Actual upper energy certificates on all 43 source endpoints at 12443. -/
namespace BstLean.Part269.N12443
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12443)
open BstLean.Part268 (cell12443)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12443 (gMinus 12443) (1 - (cell12443 i).lower) ≤ 1 ∧
    energyUpper 12443 (gMinus 12443) (BstLean.Part211.gPlus 12443)
      (finiteEnergy 12443 12443 0.011) (1 - (cell12443 i).lower) ≤
      (cell12443 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨10,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨11,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨12,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨13,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨14,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨15,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨16,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨17,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨18,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨19,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨20,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨21,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨22,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨23,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨24,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨25,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨26,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨27,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨28,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨29,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨30,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨31,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨32,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨33,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨34,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨35,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨36,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨37,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨38,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨39,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨40,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨41,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨42,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨43,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨44,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨45,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨46,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨47,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨48,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨49,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨50,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨51,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12443) (by norm_num)
        (q := 1 - (cell12443 ⟨52,by decide⟩).lower)
        (by norm_num [cell12443]) (by norm_num [cell12443])
      exact ⟨E.1,E.2.trans (by norm_num [cell12443])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12443

/-! Source-cell containment and simple scalar guards at 12443. -/
namespace BstLean.Part269.N12443
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12443)
open BstLean.Part268 (cell12443)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12443 ⟨10,by decide⟩).lower ∧ (cell12443 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12443 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12443 ⟨11,by decide⟩).lower ∧ (cell12443 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12443 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12443 ⟨12,by decide⟩).lower ∧ (cell12443 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12443 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12443 ⟨13,by decide⟩).lower ∧ (cell12443 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12443 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12443 ⟨14,by decide⟩).lower ∧ (cell12443 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12443 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12443 ⟨15,by decide⟩).lower ∧ (cell12443 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12443 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12443 ⟨16,by decide⟩).lower ∧ (cell12443 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12443 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12443 ⟨17,by decide⟩).lower ∧ (cell12443 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12443 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12443 ⟨18,by decide⟩).lower ∧ (cell12443 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12443 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12443 ⟨19,by decide⟩).lower ∧ (cell12443 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12443 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12443 ⟨20,by decide⟩).lower ∧ (cell12443 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12443 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12443 ⟨21,by decide⟩).lower ∧ (cell12443 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12443 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12443 ⟨22,by decide⟩).lower ∧ (cell12443 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12443 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12443 ⟨23,by decide⟩).lower ∧ (cell12443 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12443 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12443 ⟨24,by decide⟩).lower ∧ (cell12443 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12443 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12443 ⟨25,by decide⟩).lower ∧ (cell12443 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12443 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12443 ⟨26,by decide⟩).lower ∧ (cell12443 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12443 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12443 ⟨27,by decide⟩).lower ∧ (cell12443 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12443 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12443 ⟨28,by decide⟩).lower ∧ (cell12443 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12443 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12443 ⟨29,by decide⟩).lower ∧ (cell12443 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12443 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12443 ⟨30,by decide⟩).lower ∧ (cell12443 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12443 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12443 ⟨31,by decide⟩).lower ∧ (cell12443 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12443 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12443 ⟨32,by decide⟩).lower ∧ (cell12443 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12443 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12443 ⟨33,by decide⟩).lower ∧ (cell12443 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12443 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12443 ⟨34,by decide⟩).lower ∧ (cell12443 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12443 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12443 ⟨35,by decide⟩).lower ∧ (cell12443 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12443 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12443 ⟨36,by decide⟩).lower ∧ (cell12443 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12443 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12443 ⟨37,by decide⟩).lower ∧ (cell12443 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12443 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12443 ⟨38,by decide⟩).lower ∧ (cell12443 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12443 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12443 ⟨39,by decide⟩).lower ∧ (cell12443 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12443 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12443 ⟨40,by decide⟩).lower ∧ (cell12443 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12443 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12443 ⟨41,by decide⟩).lower ∧ (cell12443 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12443 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12443 ⟨42,by decide⟩).lower ∧ (cell12443 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12443 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12443 ⟨43,by decide⟩).lower ∧ (cell12443 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12443 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12443 ⟨44,by decide⟩).lower ∧ (cell12443 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12443 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12443 ⟨45,by decide⟩).lower ∧ (cell12443 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12443 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12443 ⟨46,by decide⟩).lower ∧ (cell12443 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12443 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12443 ⟨47,by decide⟩).lower ∧ (cell12443 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12443 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12443 ⟨48,by decide⟩).lower ∧ (cell12443 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12443 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12443 ⟨49,by decide⟩).lower ∧ (cell12443 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12443 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12443 ⟨50,by decide⟩).lower ∧ (cell12443 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12443 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12443 ⟨51,by decide⟩).lower ∧ (cell12443 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12443 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12443 ⟨52,by decide⟩).lower ∧ (cell12443 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12443 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12443 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12443 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12443,cell12443,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12443 i).lower ∧
    (cell12443 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12443 i).upper ≤ (0.532 : ℝ) ∧
    (cell12443 i).centre ≤ (0.1 : ℝ) ∧ (cell12443 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12443 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12443 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12443

/-! The local source numeric instances at 12443 have no network premises. -/
namespace BstLean.Part269.N12443
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12443)
open BstLean.Part268 (cell12443)

noncomputable def sourceNumerics12443 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12443 (cell12443 i)
      scalarRow12443.M scalarRow12443.H scalarRow12443.xi := by
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
    energy_allowance := scalarRow12443.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12443]
    centre_nonneg := (scalarRow12443.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12443])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12443
/-! Actual 12444 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12444
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12444 ≤ (1.036178938650 : ℝ) := by
  have hr : (111.552678139074 : ℝ) ≤ √(12444 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.552678139074 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12444 12444 (11 / 1000) ≤
    (0.008568930129 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12444) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.552678139074 : ℝ) ≤ √(12444 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12444)
  have hdiv : K / √(12444 : ℝ) ≤ K / 111.552678139074 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.552678139074 ≤ (0.008568930129 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12444.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12444 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12444 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12444 := gPlus_lower 12444
end BstLean.Part269.N12444

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12444
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036178938649 : ℝ) ≤ wn 12444 := by
  have hn : √(12444 : ℝ) ≤ 111.552678139075 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12444 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.552678139075 ≤ 2 / √(12444 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257154358 : ℝ) ≤ rhoBar 12444 BstLean.Part154.csC ∧
    rhoBar 12444 BstLean.Part154.csC ≤ 0.000257154756 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036178938649 : ℝ) / (1.295212 * 12444) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036178938650 : ℝ) / (1.29521 * 12444) := by gcongr
      _ ≤ (0.000257154756 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12444 BstLean.Part154.csC) ≤ 0.001028685153 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12444 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12444 BstLean.Part154.csC) (piBar (rhoBar 12444 BstLean.Part154.csC)) ≤ 0.000196416729 ∧
    cc1 (rhoBar 12444 BstLean.Part154.csC) (piBar (rhoBar 12444 BstLean.Part154.csC)) ≤ 0.000124981229 ∧
    cc2 (rhoBar 12444 BstLean.Part154.csC) ≤ 0.000072552513 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12444 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12444 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12444 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12444 BstLean.Part154.csC * nuR (rhoBar 12444 BstLean.Part154.csC)) ≤ 0.000514326044 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257154756 : ℝ) * 0.001028685153 := by gcongr
      _ ≤ (0.000514326044 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12444 BstLean.Part154.csC) * nuR (rhoBar 12444 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001028685153 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12444 BstLean.Part154.csC) * rhoBar 12444 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257154756 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257154756 / 2 + 0.399 * 0.001028685153 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196416729 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514326044 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124981229 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257154756 / 1.414213562 := by gcongr
      _ ≤ (0.000072552513 : ℝ) := by norm_num

end BstLean.Part269.N12444

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12444
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12444 BstLean.Part154.csC) (piBar (rhoBar 12444 BstLean.Part154.csC)) ≤ 1.66607E-7 := by
  have hr0 : 0 ≤ rhoBar 12444 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12444 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12444 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12444 BstLean.Part154.csC) (piBar (rhoBar 12444 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12444 BstLean.Part154.csC) (piBar (rhoBar 12444 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12444 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196416729 : ℝ) ^ 2 + 0.000124981229 ^ 2 + 3 * 0.000072552513 ^ 2 +
        2 * 0.797885 * 0.000196416729 * 0.000124981229 + 2 * 0.000196416729 * 0.000072552513 +
        4 * 0.797885 * 0.000124981229 * 0.000072552513 := by gcongr
    _ ≤ (1.66607E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12444 BstLean.Part154.csC Θ ≤ 0.002685308012 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12444 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12444 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12444 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12444 BstLean.Part154.csC) (piBar (rhoBar 12444 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12444 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036178938650 * 1.66607E-7 / (0.000257154358 : ℝ) := by gcongr
    _ ≤ 0.002685308012 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12444 BstLean.Part154.csC Θ ≤ 0.002980547199 + 0.000678530738 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12444 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12444 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12444 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036178938650 : ℝ) * ((2 * Θ * 0.000257154756 +
        (6863 / 10000) * 0.000257154756 * 12444 * 0.001028685153) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002980547199 + 0.000678530738 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12444 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12444 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12444 0.011 Θ ∧ gammaRatio 12444 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12444 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036178938650 : ℝ) * 0.525 / ((1 - 0.011) * 12444) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12444 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12444 0.011 Θ) :=
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
    badAllowance 12444 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12444 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12444 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12444 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12444 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12444 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12444 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12444 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12444 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12444 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12444 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036178938650 : ℝ) * 12444 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12444 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004180547199 + 0.003363838750 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12444

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12444
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12444 BstLean.Part154.csC) (piBar (rhoBar 12444 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12444 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12444 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12444 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12444 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12444 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12444 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12444 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12444 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12444 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12444 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12444 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12444 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12444 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12444 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053027306143 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12444) ≤ 0.010705593098 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12444 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036178938650)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010705593098 + 2 * 0.737676 / 12444) := by gcongr
    _ ≤ (0.053027306143 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12444 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12444

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12444
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491753045 : ℝ) ≤ plow 12444 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12444) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053453162543)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409786707) : eMP 12444 0.011 xi bn ≤ 0.001213430036 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12444 : ℝ) * (1 - 0.011))) ≤ 0.000599892620 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001409786707 / (12444 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599892620 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599892620 : ℝ) + 3.141593 * 0.053453162543 / (12444 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001213430036 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053453162543)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409786707) : PiBarMP 12444 12 0.011 xi bn ≤ 0.162921308052 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12444 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037547126482 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.937441830970 : ℝ) ≤ √((12444 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.552678139074 : ℝ) ≤ √(12444 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12444) ≤ 0.124895327438 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037547126482 + 0.053453162543 * 1.772454 / (2 * (110.937441830970 : ℝ))) * (1 + 0.001213430036) +
        8 / (12444 * 111.552678139074) + 0.124895327438 := by gcongr
    _ ≤ (0.162921308052 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053453162543)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409786707) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284226706106) :
    parallelOracle 12444 0.011 xi bn cd ≤ 0.163937643246 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12444 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12444 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491753045 : ℝ) ≤ plow 12444 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.552678139074 : ℝ) ≤ √(12444 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284226706106 : ℝ) / (2 * 0.560491753045 * 111.552678139074)) * 0.162921308052 +
        0.284226706106 ^ 2 / (2 * 0.560491753045 * 111.552678139074) := by gcongr
    _ ≤ (0.163937643246 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053453162543) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409786707)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284226706106) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12444 12444 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491753045 : ℝ) ≤ plow 12444 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.552678139074 : ℝ) ≤ √(12444 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12444 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12444 Θ 1.22 ≤ 0.011887661705 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.552678139074 := by gcongr <;> linarith
      _ ≤ (0.011887661705 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12444 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12444 12444 0.011 ≤ 0.008568930129 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12444 12444 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12444 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12444 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12444 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12444 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163937643246 + 0.011887661705 + (0.008568930129 : ℝ) *
        (1 + 2 * (0.284226706106 + 0.011887661705) / (0.560491753045 * 111.552678139074))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12444]

end BstLean.Part269.N12444

/-! The original eight local profiles supply actual 12444 moment certificates. -/
namespace BstLean.Part269.N12444
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12444 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12444 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12444 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053453162543 ∧
    0 ≤ bN 12444 BstLean.Part154.csC (groupTheta g) ∧ bN 12444 BstLean.Part154.csC (groupTheta g) ≤ 0.001409786707 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12444 12444 0.011
      (momentAllowance 12444 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12444 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12444 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12444 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12444 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12444 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231199399963 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12444 0.011
      (momentAllowance 12444 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12444 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12444
/-! The actual computed-centre upper energy formula at 12444. -/
namespace BstLean.Part269.N12444
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12444

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12444
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12444)
open BstLean.Part268 (cell12444)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086275688179
  | 2 => 0.087233787818
  | 3 => 0.088192411342
  | 4 => 0.089153514750
  | 5 => 0.090119444202
  | 6 => 0.091092991337
  | 7 => 0.092077453332
  | 8 => 0.093076697649
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12444 12444 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12444 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004185346396 + 0.003369149079 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S3.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12444

/-! Actual upper energy certificates on all 43 source endpoints at 12444. -/
namespace BstLean.Part269.N12444
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12444)
open BstLean.Part268 (cell12444)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12444 (gMinus 12444) (1 - (cell12444 i).lower) ≤ 1 ∧
    energyUpper 12444 (gMinus 12444) (BstLean.Part211.gPlus 12444)
      (finiteEnergy 12444 12444 0.011) (1 - (cell12444 i).lower) ≤
      (cell12444 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨10,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨11,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨12,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨13,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨14,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨15,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨16,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨17,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨18,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨19,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨20,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨21,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨22,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨23,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨24,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨25,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨26,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨27,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨28,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨29,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨30,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨31,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨32,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨33,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨34,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨35,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨36,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨37,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨38,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨39,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨40,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨41,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨42,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨43,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨44,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨45,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨46,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨47,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨48,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨49,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨50,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨51,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12444) (by norm_num)
        (q := 1 - (cell12444 ⟨52,by decide⟩).lower)
        (by norm_num [cell12444]) (by norm_num [cell12444])
      exact ⟨E.1,E.2.trans (by norm_num [cell12444])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12444

/-! Source-cell containment and simple scalar guards at 12444. -/
namespace BstLean.Part269.N12444
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12444)
open BstLean.Part268 (cell12444)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12444 ⟨10,by decide⟩).lower ∧ (cell12444 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12444 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12444 ⟨11,by decide⟩).lower ∧ (cell12444 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12444 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12444 ⟨12,by decide⟩).lower ∧ (cell12444 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12444 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12444 ⟨13,by decide⟩).lower ∧ (cell12444 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12444 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12444 ⟨14,by decide⟩).lower ∧ (cell12444 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12444 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12444 ⟨15,by decide⟩).lower ∧ (cell12444 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12444 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12444 ⟨16,by decide⟩).lower ∧ (cell12444 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12444 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12444 ⟨17,by decide⟩).lower ∧ (cell12444 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12444 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12444 ⟨18,by decide⟩).lower ∧ (cell12444 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12444 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12444 ⟨19,by decide⟩).lower ∧ (cell12444 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12444 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12444 ⟨20,by decide⟩).lower ∧ (cell12444 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12444 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12444 ⟨21,by decide⟩).lower ∧ (cell12444 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12444 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12444 ⟨22,by decide⟩).lower ∧ (cell12444 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12444 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12444 ⟨23,by decide⟩).lower ∧ (cell12444 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12444 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12444 ⟨24,by decide⟩).lower ∧ (cell12444 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12444 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12444 ⟨25,by decide⟩).lower ∧ (cell12444 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12444 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12444 ⟨26,by decide⟩).lower ∧ (cell12444 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12444 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12444 ⟨27,by decide⟩).lower ∧ (cell12444 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12444 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12444 ⟨28,by decide⟩).lower ∧ (cell12444 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12444 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12444 ⟨29,by decide⟩).lower ∧ (cell12444 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12444 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12444 ⟨30,by decide⟩).lower ∧ (cell12444 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12444 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12444 ⟨31,by decide⟩).lower ∧ (cell12444 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12444 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12444 ⟨32,by decide⟩).lower ∧ (cell12444 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12444 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12444 ⟨33,by decide⟩).lower ∧ (cell12444 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12444 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12444 ⟨34,by decide⟩).lower ∧ (cell12444 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12444 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12444 ⟨35,by decide⟩).lower ∧ (cell12444 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12444 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12444 ⟨36,by decide⟩).lower ∧ (cell12444 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12444 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12444 ⟨37,by decide⟩).lower ∧ (cell12444 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12444 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12444 ⟨38,by decide⟩).lower ∧ (cell12444 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12444 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12444 ⟨39,by decide⟩).lower ∧ (cell12444 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12444 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12444 ⟨40,by decide⟩).lower ∧ (cell12444 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12444 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12444 ⟨41,by decide⟩).lower ∧ (cell12444 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12444 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12444 ⟨42,by decide⟩).lower ∧ (cell12444 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12444 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12444 ⟨43,by decide⟩).lower ∧ (cell12444 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12444 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12444 ⟨44,by decide⟩).lower ∧ (cell12444 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12444 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12444 ⟨45,by decide⟩).lower ∧ (cell12444 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12444 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12444 ⟨46,by decide⟩).lower ∧ (cell12444 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12444 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12444 ⟨47,by decide⟩).lower ∧ (cell12444 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12444 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12444 ⟨48,by decide⟩).lower ∧ (cell12444 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12444 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12444 ⟨49,by decide⟩).lower ∧ (cell12444 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12444 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12444 ⟨50,by decide⟩).lower ∧ (cell12444 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12444 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12444 ⟨51,by decide⟩).lower ∧ (cell12444 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12444 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12444 ⟨52,by decide⟩).lower ∧ (cell12444 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12444 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12444 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12444 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12444,cell12444,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12444 i).lower ∧
    (cell12444 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12444 i).upper ≤ (0.532 : ℝ) ∧
    (cell12444 i).centre ≤ (0.1 : ℝ) ∧ (cell12444 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12444 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12444 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12444

/-! The local source numeric instances at 12444 have no network premises. -/
namespace BstLean.Part269.N12444
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12444)
open BstLean.Part268 (cell12444)

noncomputable def sourceNumerics12444 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12444 (cell12444 i)
      scalarRow12444.M scalarRow12444.H scalarRow12444.xi := by
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
    energy_allowance := scalarRow12444.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12444]
    centre_nonneg := (scalarRow12444.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12444])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12444
/-! Actual 12445 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12445
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12445 ≤ (1.036177472154 : ℝ) := by
  have hr : (111.557160236355 : ℝ) ≤ √(12445 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.557160236355 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12445 12445 (11 / 1000) ≤
    (0.008568585848 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12445) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.557160236355 : ℝ) ≤ √(12445 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12445)
  have hdiv : K / √(12445 : ℝ) ≤ K / 111.557160236355 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.557160236355 ≤ (0.008568585848 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12445.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12445 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12445 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12445 := gPlus_lower 12445
end BstLean.Part269.N12445

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12445
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036177472153 : ℝ) ≤ wn 12445 := by
  have hn : √(12445 : ℝ) ≤ 111.557160236356 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12445 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.557160236356 ≤ 2 / √(12445 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257133331 : ℝ) ≤ rhoBar 12445 BstLean.Part154.csC ∧
    rhoBar 12445 BstLean.Part154.csC ≤ 0.000257133729 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036177472153 : ℝ) / (1.295212 * 12445) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036177472154 : ℝ) / (1.29521 * 12445) := by gcongr
      _ ≤ (0.000257133729 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12445 BstLean.Part154.csC) ≤ 0.001028601034 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12445 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12445 BstLean.Part154.csC) (piBar (rhoBar 12445 BstLean.Part154.csC)) ≤ 0.000196400667 ∧
    cc1 (rhoBar 12445 BstLean.Part154.csC) (piBar (rhoBar 12445 BstLean.Part154.csC)) ≤ 0.000124971010 ∧
    cc2 (rhoBar 12445 BstLean.Part154.csC) ≤ 0.000072546581 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12445 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12445 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12445 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12445 BstLean.Part154.csC * nuR (rhoBar 12445 BstLean.Part154.csC)) ≤ 0.000514283988 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257133729 : ℝ) * 0.001028601034 := by gcongr
      _ ≤ (0.000514283988 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12445 BstLean.Part154.csC) * nuR (rhoBar 12445 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001028601034 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12445 BstLean.Part154.csC) * rhoBar 12445 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257133729 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257133729 / 2 + 0.399 * 0.001028601034 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196400667 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514283988 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124971010 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257133729 / 1.414213562 := by gcongr
      _ ≤ (0.000072546581 : ℝ) := by norm_num

end BstLean.Part269.N12445

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12445
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12445 BstLean.Part154.csC) (piBar (rhoBar 12445 BstLean.Part154.csC)) ≤ 1.66579E-7 := by
  have hr0 : 0 ≤ rhoBar 12445 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12445 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12445 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12445 BstLean.Part154.csC) (piBar (rhoBar 12445 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12445 BstLean.Part154.csC) (piBar (rhoBar 12445 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12445 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196400667 : ℝ) ^ 2 + 0.000124971010 ^ 2 + 3 * 0.000072546581 ^ 2 +
        2 * 0.797885 * 0.000196400667 * 0.000124971010 + 2 * 0.000196400667 * 0.000072546581 +
        4 * 0.797885 * 0.000124971010 * 0.000072546581 := by gcongr
    _ ≤ (1.66579E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12445 BstLean.Part154.csC Θ ≤ 0.002685072472 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12445 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12445 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12445 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12445 BstLean.Part154.csC) (piBar (rhoBar 12445 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12445 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036177472154 * 1.66579E-7 / (0.000257133331 : ℝ) := by gcongr
    _ ≤ 0.002685072472 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12445 BstLean.Part154.csC Θ ≤ 0.002980295036 + 0.000678474296 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12445 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12445 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12445 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036177472154 : ℝ) * ((2 * Θ * 0.000257133729 +
        (6863 / 10000) * 0.000257133729 * 12445 * 0.001028601034) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002980295036 + 0.000678474296 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12445 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12445 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12445 0.011 Θ ∧ gammaRatio 12445 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12445 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036177472154 : ℝ) * 0.525 / ((1 - 0.011) * 12445) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12445 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12445 0.011 Θ) :=
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
    badAllowance 12445 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12445 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12445 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12445 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12445 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12445 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12445 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12445 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12445 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12445 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12445 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036177472154 : ℝ) * 12445 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12445 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004180295036 + 0.003363546768 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12445

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12445
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12445 BstLean.Part154.csC) (piBar (rhoBar 12445 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12445 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12445 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12445 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12445 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12445 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12445 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12445 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12445 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12445 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12445 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12445 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12445 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12445 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12445 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053025152298 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12445) ≤ 0.010705162973 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12445 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036177472154)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010705162973 + 2 * 0.737676 / 12445) := by gcongr
    _ ≤ (0.053025152298 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12445 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12445

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12445
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491800144 : ℝ) ≤ plow 12445 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12445) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053452757090)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409663048) : eMP 12445 0.011 xi bn ≤ 0.001213328014 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12445 : ℝ) * (1 - 0.011))) ≤ 0.000599842209 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001409663048 / (12445 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599842209 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599842209 : ℝ) + 3.141593 * 0.053452757090 / (12445 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001213328014 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053452757090)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409663048) : PiBarMP 12445 12 0.011 xi bn ≤ 0.162914616319 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12445 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037545479728 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.941899208549 : ℝ) ≤ √((12445 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.557160236355 : ℝ) ≤ √(12445 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12445) ≤ 0.124890309446 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037545479728 + 0.053452757090 * 1.772454 / (2 * (110.941899208549 : ℝ))) * (1 + 0.001213328014) +
        8 / (12445 * 111.557160236355) + 0.124890309446 := by gcongr
    _ ≤ (0.162914616319 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053452757090)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409663048) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284223675412) :
    parallelOracle 12445 0.011 xi bn cd ≤ 0.163930877660 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12445 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12445 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491800144 : ℝ) ≤ plow 12445 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.557160236355 : ℝ) ≤ √(12445 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284223675412 : ℝ) / (2 * 0.560491800144 * 111.557160236355)) * 0.162914616319 +
        0.284223675412 ^ 2 / (2 * 0.560491800144 * 111.557160236355) := by gcongr
    _ ≤ (0.163930877660 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053452757090) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409663048)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284223675412) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12445 12445 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491800144 : ℝ) ≤ plow 12445 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.557160236355 : ℝ) ≤ √(12445 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12445 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12445 Θ 1.22 ≤ 0.011887184088 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.557160236355 := by gcongr <;> linarith
      _ ≤ (0.011887184088 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12445 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12445 12445 0.011 ≤ 0.008568585848 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12445 12445 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12445 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12445 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12445 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12445 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163930877660 + 0.011887184088 + (0.008568585848 : ℝ) *
        (1 + 2 * (0.284223675412 + 0.011887184088) / (0.560491800144 * 111.557160236355))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12445]

end BstLean.Part269.N12445

/-! The original eight local profiles supply actual 12445 moment certificates. -/
namespace BstLean.Part269.N12445
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12445 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12445 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12445 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053452757090 ∧
    0 ≤ bN 12445 BstLean.Part154.csC (groupTheta g) ∧ bN 12445 BstLean.Part154.csC (groupTheta g) ≤ 0.001409663048 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12445 12445 0.011
      (momentAllowance 12445 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12445 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12445 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12445 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12445 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12445 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231198523114 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12445 0.011
      (momentAllowance 12445 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12445 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12445
/-! The actual computed-centre upper energy formula at 12445. -/
namespace BstLean.Part269.N12445
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12445

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12445
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12445)
open BstLean.Part268 (cell12445)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086272454802
  | 2 => 0.087230487374
  | 3 => 0.088189032854
  | 4 => 0.089150044812
  | 5 => 0.090115866563
  | 6 => 0.091089286443
  | 7 => 0.092073597814
  | 8 => 0.093072663760
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12445 12445 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12445 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004185346396 + 0.003369149079 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S3.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12445

/-! Actual upper energy certificates on all 43 source endpoints at 12445. -/
namespace BstLean.Part269.N12445
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12445)
open BstLean.Part268 (cell12445)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12445 (gMinus 12445) (1 - (cell12445 i).lower) ≤ 1 ∧
    energyUpper 12445 (gMinus 12445) (BstLean.Part211.gPlus 12445)
      (finiteEnergy 12445 12445 0.011) (1 - (cell12445 i).lower) ≤
      (cell12445 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨10,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨11,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨12,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨13,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨14,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨15,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨16,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨17,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨18,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨19,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨20,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨21,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨22,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨23,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨24,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨25,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨26,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨27,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨28,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨29,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨30,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨31,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨32,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨33,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨34,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨35,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨36,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨37,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨38,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨39,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨40,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨41,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨42,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨43,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨44,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨45,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨46,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨47,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨48,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨49,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨50,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨51,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12445) (by norm_num)
        (q := 1 - (cell12445 ⟨52,by decide⟩).lower)
        (by norm_num [cell12445]) (by norm_num [cell12445])
      exact ⟨E.1,E.2.trans (by norm_num [cell12445])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12445

/-! Source-cell containment and simple scalar guards at 12445. -/
namespace BstLean.Part269.N12445
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12445)
open BstLean.Part268 (cell12445)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12445 ⟨10,by decide⟩).lower ∧ (cell12445 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12445 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12445 ⟨11,by decide⟩).lower ∧ (cell12445 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12445 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12445 ⟨12,by decide⟩).lower ∧ (cell12445 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12445 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12445 ⟨13,by decide⟩).lower ∧ (cell12445 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12445 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12445 ⟨14,by decide⟩).lower ∧ (cell12445 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12445 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12445 ⟨15,by decide⟩).lower ∧ (cell12445 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12445 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12445 ⟨16,by decide⟩).lower ∧ (cell12445 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12445 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12445 ⟨17,by decide⟩).lower ∧ (cell12445 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12445 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12445 ⟨18,by decide⟩).lower ∧ (cell12445 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12445 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12445 ⟨19,by decide⟩).lower ∧ (cell12445 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12445 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12445 ⟨20,by decide⟩).lower ∧ (cell12445 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12445 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12445 ⟨21,by decide⟩).lower ∧ (cell12445 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12445 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12445 ⟨22,by decide⟩).lower ∧ (cell12445 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12445 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12445 ⟨23,by decide⟩).lower ∧ (cell12445 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12445 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12445 ⟨24,by decide⟩).lower ∧ (cell12445 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12445 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12445 ⟨25,by decide⟩).lower ∧ (cell12445 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12445 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12445 ⟨26,by decide⟩).lower ∧ (cell12445 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12445 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12445 ⟨27,by decide⟩).lower ∧ (cell12445 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12445 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12445 ⟨28,by decide⟩).lower ∧ (cell12445 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12445 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12445 ⟨29,by decide⟩).lower ∧ (cell12445 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12445 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12445 ⟨30,by decide⟩).lower ∧ (cell12445 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12445 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12445 ⟨31,by decide⟩).lower ∧ (cell12445 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12445 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12445 ⟨32,by decide⟩).lower ∧ (cell12445 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12445 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12445 ⟨33,by decide⟩).lower ∧ (cell12445 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12445 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12445 ⟨34,by decide⟩).lower ∧ (cell12445 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12445 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12445 ⟨35,by decide⟩).lower ∧ (cell12445 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12445 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12445 ⟨36,by decide⟩).lower ∧ (cell12445 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12445 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12445 ⟨37,by decide⟩).lower ∧ (cell12445 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12445 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12445 ⟨38,by decide⟩).lower ∧ (cell12445 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12445 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12445 ⟨39,by decide⟩).lower ∧ (cell12445 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12445 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12445 ⟨40,by decide⟩).lower ∧ (cell12445 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12445 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12445 ⟨41,by decide⟩).lower ∧ (cell12445 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12445 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12445 ⟨42,by decide⟩).lower ∧ (cell12445 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12445 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12445 ⟨43,by decide⟩).lower ∧ (cell12445 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12445 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12445 ⟨44,by decide⟩).lower ∧ (cell12445 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12445 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12445 ⟨45,by decide⟩).lower ∧ (cell12445 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12445 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12445 ⟨46,by decide⟩).lower ∧ (cell12445 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12445 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12445 ⟨47,by decide⟩).lower ∧ (cell12445 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12445 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12445 ⟨48,by decide⟩).lower ∧ (cell12445 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12445 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12445 ⟨49,by decide⟩).lower ∧ (cell12445 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12445 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12445 ⟨50,by decide⟩).lower ∧ (cell12445 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12445 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12445 ⟨51,by decide⟩).lower ∧ (cell12445 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12445 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12445 ⟨52,by decide⟩).lower ∧ (cell12445 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12445 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12445 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12445 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12445,cell12445,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12445 i).lower ∧
    (cell12445 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12445 i).upper ≤ (0.532 : ℝ) ∧
    (cell12445 i).centre ≤ (0.1 : ℝ) ∧ (cell12445 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12445 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12445 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12445

/-! The local source numeric instances at 12445 have no network premises. -/
namespace BstLean.Part269.N12445
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12445)
open BstLean.Part268 (cell12445)

noncomputable def sourceNumerics12445 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12445 (cell12445 i)
      scalarRow12445.M scalarRow12445.H scalarRow12445.xi := by
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
    energy_allowance := scalarRow12445.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12445]
    centre_nonneg := (scalarRow12445.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12445])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12445
/-! Actual 12446 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12446
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12446 ≤ (1.036176005835 : ℝ) := by
  have hr : (111.561642153564 : ℝ) ≤ √(12446 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.561642153564 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12446 12446 (11 / 1000) ≤
    (0.008568241608 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12446) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.561642153564 : ℝ) ≤ √(12446 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12446)
  have hdiv : K / √(12446 : ℝ) ≤ K / 111.561642153564 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.561642153564 ≤ (0.008568241608 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12446.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12446 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12446 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12446 := gPlus_lower 12446
end BstLean.Part269.N12446

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12446
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036176005834 : ℝ) ≤ wn 12446 := by
  have hn : √(12446 : ℝ) ≤ 111.561642153565 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12446 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.561642153565 ≤ 2 / √(12446 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257112307 : ℝ) ≤ rhoBar 12446 BstLean.Part154.csC ∧
    rhoBar 12446 BstLean.Part154.csC ≤ 0.000257112705 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036176005834 : ℝ) / (1.295212 * 12446) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036176005835 : ℝ) / (1.29521 * 12446) := by gcongr
      _ ≤ (0.000257112705 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12446 BstLean.Part154.csC) ≤ 0.001028516927 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12446 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12446 BstLean.Part154.csC) (piBar (rhoBar 12446 BstLean.Part154.csC)) ≤ 0.000196384608 ∧
    cc1 (rhoBar 12446 BstLean.Part154.csC) (piBar (rhoBar 12446 BstLean.Part154.csC)) ≤ 0.000124960791 ∧
    cc2 (rhoBar 12446 BstLean.Part154.csC) ≤ 0.000072540649 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12446 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12446 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12446 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12446 BstLean.Part154.csC * nuR (rhoBar 12446 BstLean.Part154.csC)) ≤ 0.000514241937 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257112705 : ℝ) * 0.001028516927 := by gcongr
      _ ≤ (0.000514241937 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12446 BstLean.Part154.csC) * nuR (rhoBar 12446 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001028516927 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12446 BstLean.Part154.csC) * rhoBar 12446 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257112705 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257112705 / 2 + 0.399 * 0.001028516927 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196384608 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514241937 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124960791 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257112705 / 1.414213562 := by gcongr
      _ ≤ (0.000072540649 : ℝ) := by norm_num

end BstLean.Part269.N12446

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12446
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12446 BstLean.Part154.csC) (piBar (rhoBar 12446 BstLean.Part154.csC)) ≤ 1.66552E-7 := by
  have hr0 : 0 ≤ rhoBar 12446 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12446 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12446 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12446 BstLean.Part154.csC) (piBar (rhoBar 12446 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12446 BstLean.Part154.csC) (piBar (rhoBar 12446 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12446 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196384608 : ℝ) ^ 2 + 0.000124960791 ^ 2 + 3 * 0.000072540649 ^ 2 +
        2 * 0.797885 * 0.000196384608 * 0.000124960791 + 2 * 0.000196384608 * 0.000072540649 +
        4 * 0.797885 * 0.000124960791 * 0.000072540649 := by gcongr
    _ ≤ (1.66552E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12446 BstLean.Part154.csC Θ ≤ 0.002684852984 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12446 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12446 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12446 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12446 BstLean.Part154.csC) (piBar (rhoBar 12446 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12446 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036176005835 * 1.66552E-7 / (0.000257112307 : ℝ) := by gcongr
    _ ≤ 0.002684852984 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12446 BstLean.Part154.csC Θ ≤ 0.002980042906 + 0.000678417862 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12446 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12446 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12446 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036176005835 : ℝ) * ((2 * Θ * 0.000257112705 +
        (6863 / 10000) * 0.000257112705 * 12446 * 0.001028516927) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002980042906 + 0.000678417862 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12446 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12446 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12446 0.011 Θ ∧ gammaRatio 12446 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12446 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036176005835 : ℝ) * 0.525 / ((1 - 0.011) * 12446) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12446 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12446 0.011 Θ) :=
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
    badAllowance 12446 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12446 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12446 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12446 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12446 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12446 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12446 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12446 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12446 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12446 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12446 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036176005835 : ℝ) * 12446 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12446 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004180042906 + 0.003363270846 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12446

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12446
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12446 BstLean.Part154.csC) (piBar (rhoBar 12446 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12446 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12446 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12446 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12446 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12446 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12446 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12446 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12446 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12446 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12446 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12446 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12446 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12446 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12446 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053022998716 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12446) ≤ 0.010704732900 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12446 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036176005835)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010704732900 + 2 * 0.737676 / 12446) := by gcongr
    _ ≤ (0.053022998716 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12446 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12446

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12446
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491847236 : ℝ) ≤ plow 12446 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12446) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053452360101)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409547817) : eMP 12446 0.011 xi bn ≤ 0.001213229587 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12446 : ℝ) * (1 - 0.011))) ≤ 0.000599793594 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001409547817 / (12446 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599793594 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599793594 : ℝ) + 3.141593 * 0.053452360101 / (12446 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001213229587 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053452360101)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409547817) : PiBarMP 12446 12 0.011 xi bn ≤ 0.162908037705 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12446 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037543945145 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.946356407049 : ℝ) ≤ √((12446 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.561642153564 : ℝ) ≤ √(12446 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12446) ≤ 0.124885292058 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037543945145 + 0.053452360101 * 1.772454 / (2 * (110.946356407049 : ℝ))) * (1 + 0.001213229587) +
        8 / (12446 * 111.561642153564) + 0.124885292058 := by gcongr
    _ ≤ (0.162908037705 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053452360101)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409547817) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284220663283) :
    parallelOracle 12446 0.011 xi bn cd ≤ 0.163924225567 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12446 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12446 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491847236 : ℝ) ≤ plow 12446 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.561642153564 : ℝ) ≤ √(12446 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284220663283 : ℝ) / (2 * 0.560491847236 * 111.561642153564)) * 0.162908037705 +
        0.284220663283 ^ 2 / (2 * 0.560491847236 * 111.561642153564) := by gcongr
    _ ≤ (0.163924225567 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053452360101) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409547817)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284220663283) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12446 12446 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491847236 : ℝ) ≤ plow 12446 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.561642153564 : ℝ) ≤ √(12446 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12446 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12446 Θ 1.22 ≤ 0.011886706528 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.561642153564 := by gcongr <;> linarith
      _ ≤ (0.011886706528 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12446 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12446 12446 0.011 ≤ 0.008568241608 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12446 12446 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12446 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12446 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12446 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12446 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163924225567 + 0.011886706528 + (0.008568241608 : ℝ) *
        (1 + 2 * (0.284220663283 + 0.011886706528) / (0.560491847236 * 111.561642153564))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12446]

end BstLean.Part269.N12446

/-! The original eight local profiles supply actual 12446 moment certificates. -/
namespace BstLean.Part269.N12446
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12446 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12446 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12446 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053452360101 ∧
    0 ≤ bN 12446 BstLean.Part154.csC (groupTheta g) ∧ bN 12446 BstLean.Part154.csC (groupTheta g) ≤ 0.001409547817 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12446 12446 0.011
      (momentAllowance 12446 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12446 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12446 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12446 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12446 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12446 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231197664567 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12446 0.011
      (momentAllowance 12446 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12446 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12446
/-! The actual computed-centre upper energy formula at 12446. -/
namespace BstLean.Part269.N12446
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12446

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12446
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12446)
open BstLean.Part268 (cell12446)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086269222841
  | 2 => 0.087227188407
  | 3 => 0.088185655921
  | 4 => 0.089146576523
  | 5 => 0.090112290688
  | 6 => 0.091085583451
  | 7 => 0.092069744365
  | 8 => 0.093068632141
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12446 12446 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12446 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004185346396 + 0.003369149079 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S3.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12446

/-! Actual upper energy certificates on all 43 source endpoints at 12446. -/
namespace BstLean.Part269.N12446
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12446)
open BstLean.Part268 (cell12446)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12446 (gMinus 12446) (1 - (cell12446 i).lower) ≤ 1 ∧
    energyUpper 12446 (gMinus 12446) (BstLean.Part211.gPlus 12446)
      (finiteEnergy 12446 12446 0.011) (1 - (cell12446 i).lower) ≤
      (cell12446 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨10,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨11,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨12,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨13,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨14,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨15,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨16,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨17,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨18,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨19,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨20,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨21,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨22,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨23,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨24,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨25,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨26,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨27,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨28,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨29,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨30,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨31,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨32,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨33,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨34,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨35,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨36,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨37,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨38,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨39,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨40,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨41,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨42,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨43,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨44,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨45,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨46,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨47,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨48,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨49,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨50,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨51,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12446) (by norm_num)
        (q := 1 - (cell12446 ⟨52,by decide⟩).lower)
        (by norm_num [cell12446]) (by norm_num [cell12446])
      exact ⟨E.1,E.2.trans (by norm_num [cell12446])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12446

/-! Source-cell containment and simple scalar guards at 12446. -/
namespace BstLean.Part269.N12446
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12446)
open BstLean.Part268 (cell12446)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12446 ⟨10,by decide⟩).lower ∧ (cell12446 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12446 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12446 ⟨11,by decide⟩).lower ∧ (cell12446 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12446 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12446 ⟨12,by decide⟩).lower ∧ (cell12446 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12446 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12446 ⟨13,by decide⟩).lower ∧ (cell12446 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12446 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12446 ⟨14,by decide⟩).lower ∧ (cell12446 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12446 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12446 ⟨15,by decide⟩).lower ∧ (cell12446 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12446 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12446 ⟨16,by decide⟩).lower ∧ (cell12446 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12446 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12446 ⟨17,by decide⟩).lower ∧ (cell12446 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12446 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12446 ⟨18,by decide⟩).lower ∧ (cell12446 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12446 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12446 ⟨19,by decide⟩).lower ∧ (cell12446 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12446 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12446 ⟨20,by decide⟩).lower ∧ (cell12446 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12446 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12446 ⟨21,by decide⟩).lower ∧ (cell12446 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12446 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12446 ⟨22,by decide⟩).lower ∧ (cell12446 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12446 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12446 ⟨23,by decide⟩).lower ∧ (cell12446 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12446 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12446 ⟨24,by decide⟩).lower ∧ (cell12446 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12446 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12446 ⟨25,by decide⟩).lower ∧ (cell12446 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12446 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12446 ⟨26,by decide⟩).lower ∧ (cell12446 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12446 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12446 ⟨27,by decide⟩).lower ∧ (cell12446 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12446 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12446 ⟨28,by decide⟩).lower ∧ (cell12446 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12446 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12446 ⟨29,by decide⟩).lower ∧ (cell12446 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12446 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12446 ⟨30,by decide⟩).lower ∧ (cell12446 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12446 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12446 ⟨31,by decide⟩).lower ∧ (cell12446 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12446 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12446 ⟨32,by decide⟩).lower ∧ (cell12446 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12446 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12446 ⟨33,by decide⟩).lower ∧ (cell12446 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12446 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12446 ⟨34,by decide⟩).lower ∧ (cell12446 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12446 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12446 ⟨35,by decide⟩).lower ∧ (cell12446 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12446 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12446 ⟨36,by decide⟩).lower ∧ (cell12446 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12446 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12446 ⟨37,by decide⟩).lower ∧ (cell12446 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12446 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12446 ⟨38,by decide⟩).lower ∧ (cell12446 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12446 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12446 ⟨39,by decide⟩).lower ∧ (cell12446 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12446 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12446 ⟨40,by decide⟩).lower ∧ (cell12446 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12446 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12446 ⟨41,by decide⟩).lower ∧ (cell12446 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12446 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12446 ⟨42,by decide⟩).lower ∧ (cell12446 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12446 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12446 ⟨43,by decide⟩).lower ∧ (cell12446 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12446 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12446 ⟨44,by decide⟩).lower ∧ (cell12446 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12446 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12446 ⟨45,by decide⟩).lower ∧ (cell12446 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12446 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12446 ⟨46,by decide⟩).lower ∧ (cell12446 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12446 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12446 ⟨47,by decide⟩).lower ∧ (cell12446 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12446 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12446 ⟨48,by decide⟩).lower ∧ (cell12446 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12446 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12446 ⟨49,by decide⟩).lower ∧ (cell12446 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12446 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12446 ⟨50,by decide⟩).lower ∧ (cell12446 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12446 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12446 ⟨51,by decide⟩).lower ∧ (cell12446 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12446 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12446 ⟨52,by decide⟩).lower ∧ (cell12446 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12446 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12446 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12446 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12446,cell12446,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12446 i).lower ∧
    (cell12446 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12446 i).upper ≤ (0.532 : ℝ) ∧
    (cell12446 i).centre ≤ (0.1 : ℝ) ∧ (cell12446 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12446 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12446 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12446

/-! The local source numeric instances at 12446 have no network premises. -/
namespace BstLean.Part269.N12446
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12446)
open BstLean.Part268 (cell12446)

noncomputable def sourceNumerics12446 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12446 (cell12446 i)
      scalarRow12446.M scalarRow12446.H scalarRow12446.xi := by
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
    energy_allowance := scalarRow12446.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12446]
    centre_nonneg := (scalarRow12446.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12446])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12446
/-! Actual 12447 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12447
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12447 ≤ (1.036174539694 : ℝ) := by
  have hr : (111.566123890722 : ℝ) ≤ √(12447 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.566123890722 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12447 12447 (11 / 1000) ≤
    (0.008567897409 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12447) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.566123890722 : ℝ) ≤ √(12447 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12447)
  have hdiv : K / √(12447 : ℝ) ≤ K / 111.566123890722 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.566123890722 ≤ (0.008567897409 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12447.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12447 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12447 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12447 := gPlus_lower 12447
end BstLean.Part269.N12447

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12447
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036174539693 : ℝ) ≤ wn 12447 := by
  have hn : √(12447 : ℝ) ≤ 111.566123890723 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12447 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.566123890723 ≤ 2 / √(12447 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257091287 : ℝ) ≤ rhoBar 12447 BstLean.Part154.csC ∧
    rhoBar 12447 BstLean.Part154.csC ≤ 0.000257091685 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036174539693 : ℝ) / (1.295212 * 12447) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036174539694 : ℝ) / (1.29521 * 12447) := by gcongr
      _ ≤ (0.000257091685 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12447 BstLean.Part154.csC) ≤ 0.001028432837 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12447 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12447 BstLean.Part154.csC) (piBar (rhoBar 12447 BstLean.Part154.csC)) ≤ 0.000196368552 ∧
    cc1 (rhoBar 12447 BstLean.Part154.csC) (piBar (rhoBar 12447 BstLean.Part154.csC)) ≤ 0.000124950575 ∧
    cc2 (rhoBar 12447 BstLean.Part154.csC) ≤ 0.000072534719 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12447 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12447 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12447 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12447 BstLean.Part154.csC * nuR (rhoBar 12447 BstLean.Part154.csC)) ≤ 0.000514199894 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257091685 : ℝ) * 0.001028432837 := by gcongr
      _ ≤ (0.000514199894 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12447 BstLean.Part154.csC) * nuR (rhoBar 12447 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001028432837 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12447 BstLean.Part154.csC) * rhoBar 12447 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257091685 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257091685 / 2 + 0.399 * 0.001028432837 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196368552 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514199894 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124950575 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257091685 / 1.414213562 := by gcongr
      _ ≤ (0.000072534719 : ℝ) := by norm_num

end BstLean.Part269.N12447

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12447
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12447 BstLean.Part154.csC) (piBar (rhoBar 12447 BstLean.Part154.csC)) ≤ 1.66525E-7 := by
  have hr0 : 0 ≤ rhoBar 12447 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12447 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12447 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12447 BstLean.Part154.csC) (piBar (rhoBar 12447 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12447 BstLean.Part154.csC) (piBar (rhoBar 12447 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12447 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196368552 : ℝ) ^ 2 + 0.000124950575 ^ 2 + 3 * 0.000072534719 ^ 2 +
        2 * 0.797885 * 0.000196368552 * 0.000124950575 + 2 * 0.000196368552 * 0.000072534719 +
        4 * 0.797885 * 0.000124950575 * 0.000072534719 := by gcongr
    _ ≤ (1.66525E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12447 BstLean.Part154.csC Θ ≤ 0.002684633420 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12447 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12447 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12447 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12447 BstLean.Part154.csC) (piBar (rhoBar 12447 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12447 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036174539694 * 1.66525E-7 / (0.000257091287 : ℝ) := by gcongr
    _ ≤ 0.002684633420 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12447 BstLean.Part154.csC Θ ≤ 0.002979790834 + 0.000678361439 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12447 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12447 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12447 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036174539694 : ℝ) * ((2 * Θ * 0.000257091685 +
        (6863 / 10000) * 0.000257091685 * 12447 * 0.001028432837) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002979790834 + 0.000678361439 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12447 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12447 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12447 0.011 Θ ∧ gammaRatio 12447 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12447 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036174539694 : ℝ) * 0.525 / ((1 - 0.011) * 12447) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12447 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12447 0.011 Θ) :=
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
    badAllowance 12447 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12447 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12447 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12447 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12447 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12447 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12447 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12447 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12447 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12447 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12447 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036174539694 : ℝ) * 12447 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12447 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004179790834 + 0.003362994859 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12447

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12447
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12447 BstLean.Part154.csC) (piBar (rhoBar 12447 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12447 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12447 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12447 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12447 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12447 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12447 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12447 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12447 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12447 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12447 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12447 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12447 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12447 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12447 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053020845396 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12447) ≤ 0.010704302879 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12447 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036174539694)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010704302879 + 2 * 0.737676 / 12447) := by gcongr
    _ ≤ (0.053020845396 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12447 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12447

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12447
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491894319 : ℝ) ≤ plow 12447 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12447) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053451963135)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409432546) : eMP 12447 0.011 xi bn ≤ 0.001213131151 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12447 : ℝ) * (1 - 0.011))) ≤ 0.000599744975 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001409432546 / (12447 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599744975 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599744975 : ℝ) + 3.141593 * 0.053451963135 / (12447 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001213131151 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053451963135)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409432546) : PiBarMP 12447 12 0.011 xi bn ≤ 0.162901459101 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12447 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037542409966 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.950813426490 : ℝ) ≤ √((12447 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.566123890722 : ℝ) ≤ √(12447 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12447) ≤ 0.124880275275 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037542409966 + 0.053451963135 * 1.772454 / (2 * (110.950813426490 : ℝ))) * (1 + 0.001213131151) +
        8 / (12447 * 111.566123890722) + 0.124880275275 := by gcongr
    _ ≤ (0.162901459101 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053451963135)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409432546) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284217651462) :
    parallelOracle 12447 0.011 xi bn cd ≤ 0.163917573493 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12447 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12447 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491894319 : ℝ) ≤ plow 12447 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.566123890722 : ℝ) ≤ √(12447 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284217651462 : ℝ) / (2 * 0.560491894319 * 111.566123890722)) * 0.162901459101 +
        0.284217651462 ^ 2 / (2 * 0.560491894319 * 111.566123890722) := by gcongr
    _ ≤ (0.163917573493 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053451963135) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409432546)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284217651462) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12447 12447 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491894319 : ℝ) ≤ plow 12447 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.566123890722 : ℝ) ≤ √(12447 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12447 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12447 Θ 1.22 ≤ 0.011886229026 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.566123890722 := by gcongr <;> linarith
      _ ≤ (0.011886229026 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12447 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12447 12447 0.011 ≤ 0.008567897409 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12447 12447 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12447 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12447 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12447 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12447 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163917573493 + 0.011886229026 + (0.008567897409 : ℝ) *
        (1 + 2 * (0.284217651462 + 0.011886229026) / (0.560491894319 * 111.566123890722))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12447]

end BstLean.Part269.N12447

/-! The original eight local profiles supply actual 12447 moment certificates. -/
namespace BstLean.Part269.N12447
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12447 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12447 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12447 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053451963135 ∧
    0 ≤ bN 12447 BstLean.Part154.csC (groupTheta g) ∧ bN 12447 BstLean.Part154.csC (groupTheta g) ≤ 0.001409432546 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12447 12447 0.011
      (momentAllowance 12447 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12447 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12447 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12447 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12447 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12447 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231196806066 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12447 0.011
      (momentAllowance 12447 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12447 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12447
/-! The actual computed-centre upper energy formula at 12447. -/
namespace BstLean.Part269.N12447
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12447

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12447
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12447)
open BstLean.Part268 (cell12447)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086265992294
  | 2 => 0.087223890917
  | 3 => 0.088182280541
  | 4 => 0.089143109880
  | 5 => 0.090108716572
  | 6 => 0.091081882358
  | 7 => 0.092065892982
  | 8 => 0.093064602788
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12447 12447 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12447 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004185346396 + 0.003369149079 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S3.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12447

/-! Actual upper energy certificates on all 43 source endpoints at 12447. -/
namespace BstLean.Part269.N12447
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12447)
open BstLean.Part268 (cell12447)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12447 (gMinus 12447) (1 - (cell12447 i).lower) ≤ 1 ∧
    energyUpper 12447 (gMinus 12447) (BstLean.Part211.gPlus 12447)
      (finiteEnergy 12447 12447 0.011) (1 - (cell12447 i).lower) ≤
      (cell12447 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨10,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨11,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨12,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨13,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨14,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨15,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨16,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨17,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨18,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨19,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨20,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨21,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨22,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨23,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨24,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨25,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨26,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨27,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨28,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨29,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨30,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨31,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨32,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨33,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨34,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨35,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨36,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨37,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨38,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨39,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨40,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨41,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨42,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨43,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨44,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨45,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨46,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨47,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨48,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨49,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨50,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨51,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12447) (by norm_num)
        (q := 1 - (cell12447 ⟨52,by decide⟩).lower)
        (by norm_num [cell12447]) (by norm_num [cell12447])
      exact ⟨E.1,E.2.trans (by norm_num [cell12447])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12447

/-! Source-cell containment and simple scalar guards at 12447. -/
namespace BstLean.Part269.N12447
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12447)
open BstLean.Part268 (cell12447)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12447 ⟨10,by decide⟩).lower ∧ (cell12447 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12447 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12447 ⟨11,by decide⟩).lower ∧ (cell12447 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12447 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12447 ⟨12,by decide⟩).lower ∧ (cell12447 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12447 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12447 ⟨13,by decide⟩).lower ∧ (cell12447 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12447 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12447 ⟨14,by decide⟩).lower ∧ (cell12447 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12447 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12447 ⟨15,by decide⟩).lower ∧ (cell12447 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12447 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12447 ⟨16,by decide⟩).lower ∧ (cell12447 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12447 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12447 ⟨17,by decide⟩).lower ∧ (cell12447 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12447 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12447 ⟨18,by decide⟩).lower ∧ (cell12447 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12447 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12447 ⟨19,by decide⟩).lower ∧ (cell12447 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12447 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12447 ⟨20,by decide⟩).lower ∧ (cell12447 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12447 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12447 ⟨21,by decide⟩).lower ∧ (cell12447 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12447 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12447 ⟨22,by decide⟩).lower ∧ (cell12447 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12447 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12447 ⟨23,by decide⟩).lower ∧ (cell12447 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12447 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12447 ⟨24,by decide⟩).lower ∧ (cell12447 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12447 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12447 ⟨25,by decide⟩).lower ∧ (cell12447 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12447 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12447 ⟨26,by decide⟩).lower ∧ (cell12447 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12447 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12447 ⟨27,by decide⟩).lower ∧ (cell12447 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12447 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12447 ⟨28,by decide⟩).lower ∧ (cell12447 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12447 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12447 ⟨29,by decide⟩).lower ∧ (cell12447 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12447 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12447 ⟨30,by decide⟩).lower ∧ (cell12447 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12447 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12447 ⟨31,by decide⟩).lower ∧ (cell12447 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12447 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12447 ⟨32,by decide⟩).lower ∧ (cell12447 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12447 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12447 ⟨33,by decide⟩).lower ∧ (cell12447 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12447 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12447 ⟨34,by decide⟩).lower ∧ (cell12447 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12447 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12447 ⟨35,by decide⟩).lower ∧ (cell12447 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12447 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12447 ⟨36,by decide⟩).lower ∧ (cell12447 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12447 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12447 ⟨37,by decide⟩).lower ∧ (cell12447 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12447 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12447 ⟨38,by decide⟩).lower ∧ (cell12447 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12447 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12447 ⟨39,by decide⟩).lower ∧ (cell12447 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12447 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12447 ⟨40,by decide⟩).lower ∧ (cell12447 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12447 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12447 ⟨41,by decide⟩).lower ∧ (cell12447 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12447 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12447 ⟨42,by decide⟩).lower ∧ (cell12447 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12447 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12447 ⟨43,by decide⟩).lower ∧ (cell12447 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12447 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12447 ⟨44,by decide⟩).lower ∧ (cell12447 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12447 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12447 ⟨45,by decide⟩).lower ∧ (cell12447 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12447 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12447 ⟨46,by decide⟩).lower ∧ (cell12447 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12447 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12447 ⟨47,by decide⟩).lower ∧ (cell12447 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12447 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12447 ⟨48,by decide⟩).lower ∧ (cell12447 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12447 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12447 ⟨49,by decide⟩).lower ∧ (cell12447 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12447 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12447 ⟨50,by decide⟩).lower ∧ (cell12447 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12447 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12447 ⟨51,by decide⟩).lower ∧ (cell12447 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12447 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12447 ⟨52,by decide⟩).lower ∧ (cell12447 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12447 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12447 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12447 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12447,cell12447,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12447 i).lower ∧
    (cell12447 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12447 i).upper ≤ (0.532 : ℝ) ∧
    (cell12447 i).centre ≤ (0.1 : ℝ) ∧ (cell12447 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12447 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12447 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12447

/-! The local source numeric instances at 12447 have no network premises. -/
namespace BstLean.Part269.N12447
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12447)
open BstLean.Part268 (cell12447)

noncomputable def sourceNumerics12447 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12447 (cell12447 i)
      scalarRow12447.M scalarRow12447.H scalarRow12447.xi := by
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
    energy_allowance := scalarRow12447.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12447]
    centre_nonneg := (scalarRow12447.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12447])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12447
/-! Actual 12448 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12448
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12448 ≤ (1.036173073731 : ℝ) := by
  have hr : (111.570605447850 : ℝ) ≤ √(12448 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.570605447850 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12448 12448 (11 / 1000) ≤
    (0.008567553252 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12448) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.570605447850 : ℝ) ≤ √(12448 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12448)
  have hdiv : K / √(12448 : ℝ) ≤ K / 111.570605447850 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.570605447850 ≤ (0.008567553252 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12448.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12448 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12448 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12448 := gPlus_lower 12448
end BstLean.Part269.N12448

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12448
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036173073730 : ℝ) ≤ wn 12448 := by
  have hn : √(12448 : ℝ) ≤ 111.570605447851 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12448 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.570605447851 ≤ 2 / √(12448 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257070270 : ℝ) ≤ rhoBar 12448 BstLean.Part154.csC ∧
    rhoBar 12448 BstLean.Part154.csC ≤ 0.000257070668 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036173073730 : ℝ) / (1.295212 * 12448) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036173073731 : ℝ) / (1.29521 * 12448) := by gcongr
      _ ≤ (0.000257070668 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12448 BstLean.Part154.csC) ≤ 0.001028348758 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12448 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12448 BstLean.Part154.csC) (piBar (rhoBar 12448 BstLean.Part154.csC)) ≤ 0.000196352499 ∧
    cc1 (rhoBar 12448 BstLean.Part154.csC) (piBar (rhoBar 12448 BstLean.Part154.csC)) ≤ 0.000124940360 ∧
    cc2 (rhoBar 12448 BstLean.Part154.csC) ≤ 0.000072528789 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12448 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12448 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12448 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12448 BstLean.Part154.csC * nuR (rhoBar 12448 BstLean.Part154.csC)) ≤ 0.000514157858 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257070668 : ℝ) * 0.001028348758 := by gcongr
      _ ≤ (0.000514157858 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12448 BstLean.Part154.csC) * nuR (rhoBar 12448 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001028348758 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12448 BstLean.Part154.csC) * rhoBar 12448 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257070668 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257070668 / 2 + 0.399 * 0.001028348758 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196352499 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514157858 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124940360 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257070668 / 1.414213562 := by gcongr
      _ ≤ (0.000072528789 : ℝ) := by norm_num

end BstLean.Part269.N12448

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12448
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12448 BstLean.Part154.csC) (piBar (rhoBar 12448 BstLean.Part154.csC)) ≤ 1.66498E-7 := by
  have hr0 : 0 ≤ rhoBar 12448 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12448 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12448 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12448 BstLean.Part154.csC) (piBar (rhoBar 12448 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12448 BstLean.Part154.csC) (piBar (rhoBar 12448 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12448 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196352499 : ℝ) ^ 2 + 0.000124940360 ^ 2 + 3 * 0.000072528789 ^ 2 +
        2 * 0.797885 * 0.000196352499 * 0.000124940360 + 2 * 0.000196352499 * 0.000072528789 +
        4 * 0.797885 * 0.000124940360 * 0.000072528789 := by gcongr
    _ ≤ (1.66498E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12448 BstLean.Part154.csC Θ ≤ 0.002684413790 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12448 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12448 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12448 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12448 BstLean.Part154.csC) (piBar (rhoBar 12448 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12448 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036173073731 * 1.66498E-7 / (0.000257070270 : ℝ) := by gcongr
    _ ≤ 0.002684413790 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12448 BstLean.Part154.csC Θ ≤ 0.002979538791 + 0.000678305024 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12448 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12448 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12448 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036173073731 : ℝ) * ((2 * Θ * 0.000257070668 +
        (6863 / 10000) * 0.000257070668 * 12448 * 0.001028348758) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002979538791 + 0.000678305024 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12448 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12448 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12448 0.011 Θ ∧ gammaRatio 12448 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12448 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036173073731 : ℝ) * 0.525 / ((1 - 0.011) * 12448) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12448 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12448 0.011 Θ) :=
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
    badAllowance 12448 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12448 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12448 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12448 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12448 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12448 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12448 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12448 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12448 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12448 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12448 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036173073731 : ℝ) * 12448 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12448 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004179538791 + 0.003362718814 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12448

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12448
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12448 BstLean.Part154.csC) (piBar (rhoBar 12448 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12448 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12448 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12448 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12448 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12448 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12448 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12448 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12448 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12448 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12448 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12448 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12448 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12448 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12448 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053018692333 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12448) ≤ 0.010703872909 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12448 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036173073731)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010703872909 + 2 * 0.737676 / 12448) := by gcongr
    _ ≤ (0.053018692333 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12448 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12448

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12448
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491941396 : ℝ) ≤ plow 12448 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12448) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053451566169)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409317240) : eMP 12448 0.011 xi bn ≤ 0.001213032708 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12448 : ℝ) * (1 - 0.011))) ≤ 0.000599696352 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001409317240 / (12448 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599696352 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599696352 : ℝ) + 3.141593 * 0.053451566169 / (12448 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001213032708 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053451566169)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409317240) : PiBarMP 12448 12 0.011 xi bn ≤ 0.162894880574 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12448 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037540874258 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.955270266896 : ℝ) ≤ √((12448 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.570605447850 : ℝ) ≤ √(12448 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12448) ≤ 0.124875259096 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037540874258 + 0.053451566169 * 1.772454 / (2 * (110.955270266896 : ℝ))) * (1 + 0.001213032708) +
        8 / (12448 * 111.570605447850) + 0.124875259096 := by gcongr
    _ ≤ (0.162894880574 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053451566169)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409317240) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284214639895) :
    parallelOracle 12448 0.011 xi bn cd ≤ 0.163910921506 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12448 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12448 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491941396 : ℝ) ≤ plow 12448 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.570605447850 : ℝ) ≤ √(12448 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284214639895 : ℝ) / (2 * 0.560491941396 * 111.570605447850)) * 0.162894880574 +
        0.284214639895 ^ 2 / (2 * 0.560491941396 * 111.570605447850) := by gcongr
    _ ≤ (0.163910921506 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053451566169) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409317240)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284214639895) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12448 12448 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491941396 : ℝ) ≤ plow 12448 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.570605447850 : ℝ) ≤ √(12448 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12448 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12448 Θ 1.22 ≤ 0.011885751581 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.570605447850 := by gcongr <;> linarith
      _ ≤ (0.011885751581 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12448 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12448 12448 0.011 ≤ 0.008567553252 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12448 12448 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12448 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12448 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12448 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12448 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163910921506 + 0.011885751581 + (0.008567553252 : ℝ) *
        (1 + 2 * (0.284214639895 + 0.011885751581) / (0.560491941396 * 111.570605447850))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12448]

end BstLean.Part269.N12448

/-! The original eight local profiles supply actual 12448 moment certificates. -/
namespace BstLean.Part269.N12448
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12448 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12448 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12448 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053451566169 ∧
    0 ≤ bN 12448 BstLean.Part154.csC (groupTheta g) ∧ bN 12448 BstLean.Part154.csC (groupTheta g) ≤ 0.001409317240 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12448 12448 0.011
      (momentAllowance 12448 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12448 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12448 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12448 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12448 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12448 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231195947562 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12448 0.011
      (momentAllowance 12448 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12448 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12448
/-! The actual computed-centre upper energy formula at 12448. -/
namespace BstLean.Part269.N12448
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12448

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12448
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12448)
open BstLean.Part268 (cell12448)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086262763160
  | 2 => 0.087220594901
  | 3 => 0.088178906711
  | 4 => 0.089139644881
  | 5 => 0.090105144216
  | 6 => 0.091078183162
  | 7 => 0.092062043662
  | 8 => 0.093060575698
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12448 12448 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12448 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004185346396 + 0.003369149079 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S3.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12448

/-! Actual upper energy certificates on all 43 source endpoints at 12448. -/
namespace BstLean.Part269.N12448
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12448)
open BstLean.Part268 (cell12448)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12448 (gMinus 12448) (1 - (cell12448 i).lower) ≤ 1 ∧
    energyUpper 12448 (gMinus 12448) (BstLean.Part211.gPlus 12448)
      (finiteEnergy 12448 12448 0.011) (1 - (cell12448 i).lower) ≤
      (cell12448 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨10,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨11,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨12,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨13,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨14,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨15,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨16,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨17,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨18,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨19,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨20,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨21,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨22,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨23,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨24,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨25,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨26,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨27,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨28,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨29,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨30,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨31,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨32,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨33,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨34,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨35,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨36,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨37,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨38,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨39,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨40,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨41,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨42,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨43,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨44,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨45,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨46,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨47,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨48,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨49,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨50,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨51,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12448) (by norm_num)
        (q := 1 - (cell12448 ⟨52,by decide⟩).lower)
        (by norm_num [cell12448]) (by norm_num [cell12448])
      exact ⟨E.1,E.2.trans (by norm_num [cell12448])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12448

/-! Source-cell containment and simple scalar guards at 12448. -/
namespace BstLean.Part269.N12448
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12448)
open BstLean.Part268 (cell12448)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12448 ⟨10,by decide⟩).lower ∧ (cell12448 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12448 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12448 ⟨11,by decide⟩).lower ∧ (cell12448 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12448 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12448 ⟨12,by decide⟩).lower ∧ (cell12448 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12448 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12448 ⟨13,by decide⟩).lower ∧ (cell12448 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12448 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12448 ⟨14,by decide⟩).lower ∧ (cell12448 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12448 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12448 ⟨15,by decide⟩).lower ∧ (cell12448 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12448 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12448 ⟨16,by decide⟩).lower ∧ (cell12448 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12448 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12448 ⟨17,by decide⟩).lower ∧ (cell12448 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12448 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12448 ⟨18,by decide⟩).lower ∧ (cell12448 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12448 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12448 ⟨19,by decide⟩).lower ∧ (cell12448 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12448 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12448 ⟨20,by decide⟩).lower ∧ (cell12448 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12448 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12448 ⟨21,by decide⟩).lower ∧ (cell12448 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12448 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12448 ⟨22,by decide⟩).lower ∧ (cell12448 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12448 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12448 ⟨23,by decide⟩).lower ∧ (cell12448 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12448 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12448 ⟨24,by decide⟩).lower ∧ (cell12448 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12448 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12448 ⟨25,by decide⟩).lower ∧ (cell12448 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12448 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12448 ⟨26,by decide⟩).lower ∧ (cell12448 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12448 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12448 ⟨27,by decide⟩).lower ∧ (cell12448 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12448 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12448 ⟨28,by decide⟩).lower ∧ (cell12448 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12448 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12448 ⟨29,by decide⟩).lower ∧ (cell12448 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12448 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12448 ⟨30,by decide⟩).lower ∧ (cell12448 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12448 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12448 ⟨31,by decide⟩).lower ∧ (cell12448 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12448 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12448 ⟨32,by decide⟩).lower ∧ (cell12448 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12448 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12448 ⟨33,by decide⟩).lower ∧ (cell12448 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12448 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12448 ⟨34,by decide⟩).lower ∧ (cell12448 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12448 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12448 ⟨35,by decide⟩).lower ∧ (cell12448 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12448 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12448 ⟨36,by decide⟩).lower ∧ (cell12448 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12448 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12448 ⟨37,by decide⟩).lower ∧ (cell12448 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12448 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12448 ⟨38,by decide⟩).lower ∧ (cell12448 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12448 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12448 ⟨39,by decide⟩).lower ∧ (cell12448 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12448 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12448 ⟨40,by decide⟩).lower ∧ (cell12448 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12448 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12448 ⟨41,by decide⟩).lower ∧ (cell12448 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12448 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12448 ⟨42,by decide⟩).lower ∧ (cell12448 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12448 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12448 ⟨43,by decide⟩).lower ∧ (cell12448 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12448 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12448 ⟨44,by decide⟩).lower ∧ (cell12448 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12448 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12448 ⟨45,by decide⟩).lower ∧ (cell12448 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12448 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12448 ⟨46,by decide⟩).lower ∧ (cell12448 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12448 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12448 ⟨47,by decide⟩).lower ∧ (cell12448 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12448 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12448 ⟨48,by decide⟩).lower ∧ (cell12448 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12448 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12448 ⟨49,by decide⟩).lower ∧ (cell12448 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12448 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12448 ⟨50,by decide⟩).lower ∧ (cell12448 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12448 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12448 ⟨51,by decide⟩).lower ∧ (cell12448 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12448 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12448 ⟨52,by decide⟩).lower ∧ (cell12448 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12448 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12448 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12448 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12448,cell12448,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12448 i).lower ∧
    (cell12448 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12448 i).upper ≤ (0.532 : ℝ) ∧
    (cell12448 i).centre ≤ (0.1 : ℝ) ∧ (cell12448 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12448 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12448 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12448

/-! The local source numeric instances at 12448 have no network premises. -/
namespace BstLean.Part269.N12448
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12448)
open BstLean.Part268 (cell12448)

noncomputable def sourceNumerics12448 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12448 (cell12448 i)
      scalarRow12448.M scalarRow12448.H scalarRow12448.xi := by
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
    energy_allowance := scalarRow12448.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12448]
    centre_nonneg := (scalarRow12448.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12448])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12448
/-! Actual 12449 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12449
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12449 ≤ (1.036171607945 : ℝ) := by
  have hr : (111.575086824971 : ℝ) ≤ √(12449 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.575086824971 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12449 12449 (11 / 1000) ≤
    (0.008567209136 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12449) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.575086824971 : ℝ) ≤ √(12449 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12449)
  have hdiv : K / √(12449 : ℝ) ≤ K / 111.575086824971 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.575086824971 ≤ (0.008567209136 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12449.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12449 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12449 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12449 := gPlus_lower 12449
end BstLean.Part269.N12449

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12449
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036171607944 : ℝ) ≤ wn 12449 := by
  have hn : √(12449 : ℝ) ≤ 111.575086824972 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12449 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.575086824972 ≤ 2 / √(12449 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257049257 : ℝ) ≤ rhoBar 12449 BstLean.Part154.csC ∧
    rhoBar 12449 BstLean.Part154.csC ≤ 0.000257049654 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036171607944 : ℝ) / (1.295212 * 12449) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036171607945 : ℝ) / (1.29521 * 12449) := by gcongr
      _ ≤ (0.000257049654 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12449 BstLean.Part154.csC) ≤ 0.001028264691 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12449 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12449 BstLean.Part154.csC) (piBar (rhoBar 12449 BstLean.Part154.csC)) ≤ 0.000196336447 ∧
    cc1 (rhoBar 12449 BstLean.Part154.csC) (piBar (rhoBar 12449 BstLean.Part154.csC)) ≤ 0.000124930146 ∧
    cc2 (rhoBar 12449 BstLean.Part154.csC) ≤ 0.000072522860 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12449 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12449 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12449 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12449 BstLean.Part154.csC * nuR (rhoBar 12449 BstLean.Part154.csC)) ≤ 0.000514115827 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257049654 : ℝ) * 0.001028264691 := by gcongr
      _ ≤ (0.000514115827 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12449 BstLean.Part154.csC) * nuR (rhoBar 12449 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001028264691 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12449 BstLean.Part154.csC) * rhoBar 12449 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257049654 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257049654 / 2 + 0.399 * 0.001028264691 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196336447 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514115827 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124930146 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257049654 / 1.414213562 := by gcongr
      _ ≤ (0.000072522860 : ℝ) := by norm_num

end BstLean.Part269.N12449

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12449
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12449 BstLean.Part154.csC) (piBar (rhoBar 12449 BstLean.Part154.csC)) ≤ 1.66470E-7 := by
  have hr0 : 0 ≤ rhoBar 12449 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12449 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12449 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12449 BstLean.Part154.csC) (piBar (rhoBar 12449 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12449 BstLean.Part154.csC) (piBar (rhoBar 12449 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12449 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196336447 : ℝ) ^ 2 + 0.000124930146 ^ 2 + 3 * 0.000072522860 ^ 2 +
        2 * 0.797885 * 0.000196336447 * 0.000124930146 + 2 * 0.000196336447 * 0.000072522860 +
        4 * 0.797885 * 0.000124930146 * 0.000072522860 := by gcongr
    _ ≤ (1.66470E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12449 BstLean.Part154.csC Θ ≤ 0.002684177961 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12449 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12449 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12449 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12449 BstLean.Part154.csC) (piBar (rhoBar 12449 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12449 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036171607945 * 1.66470E-7 / (0.000257049257 : ℝ) := by gcongr
    _ ≤ 0.002684177961 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12449 BstLean.Part154.csC Θ ≤ 0.002979286781 + 0.000678248617 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12449 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12449 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12449 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036171607945 : ℝ) * ((2 * Θ * 0.000257049654 +
        (6863 / 10000) * 0.000257049654 * 12449 * 0.001028264691) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002979286781 + 0.000678248617 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12449 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12449 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12449 0.011 Θ ∧ gammaRatio 12449 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12449 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036171607945 : ℝ) * 0.525 / ((1 - 0.011) * 12449) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12449 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12449 0.011 Θ) :=
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
    badAllowance 12449 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12449 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12449 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12449 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12449 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12449 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12449 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12449 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12449 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12449 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12449 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036171607945 : ℝ) * 12449 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12449 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004179286781 + 0.003362426578 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12449

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12449
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12449 BstLean.Part154.csC) (piBar (rhoBar 12449 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12449 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12449 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12449 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12449 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12449 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12449 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12449 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12449 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12449 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12449 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12449 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12449 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12449 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12449 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053016539537 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12449) ≤ 0.010703442992 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12449 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036171607945)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010703442992 + 2 * 0.737676 / 12449) := by gcongr
    _ ≤ (0.053016539537 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12449 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12449

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12449
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491988464 : ℝ) ≤ plow 12449 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12449) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053451160735)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409193430) : eMP 12449 0.011 xi bn ≤ 0.001212930653 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12449 : ℝ) * (1 - 0.011))) ≤ 0.000599645924 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001409193430 / (12449 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599645924 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599645924 : ℝ) + 3.141593 * 0.053451160735 / (12449 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001212930653 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053451160735)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409193430) : PiBarMP 12449 12 0.011 xi bn ≤ 0.162888188981 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12449 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037539225219 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.959726928286 : ℝ) ≤ √((12449 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.575086824971 : ℝ) ≤ √(12449 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12449) ≤ 0.124870243522 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037539225219 + 0.053451160735 * 1.772454 / (2 * (110.959726928286 : ℝ))) * (1 + 0.001212930653) +
        8 / (12449 * 111.575086824971) + 0.124870243522 := by gcongr
    _ ≤ (0.162888188981 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053451160735)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409193430) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284211610279) :
    parallelOracle 12449 0.011 xi bn cd ≤ 0.163904156098 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12449 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12449 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491988464 : ℝ) ≤ plow 12449 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.575086824971 : ℝ) ≤ √(12449 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284211610279 : ℝ) / (2 * 0.560491988464 * 111.575086824971)) * 0.162888188981 +
        0.284211610279 ^ 2 / (2 * 0.560491988464 * 111.575086824971) := by gcongr
    _ ≤ (0.163904156098 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053451160735) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409193430)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284211610279) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12449 12449 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491988464 : ℝ) ≤ plow 12449 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.575086824971 : ℝ) ≤ √(12449 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12449 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12449 Θ 1.22 ≤ 0.011885274193 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.575086824971 := by gcongr <;> linarith
      _ ≤ (0.011885274193 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12449 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12449 12449 0.011 ≤ 0.008567209136 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12449 12449 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12449 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12449 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12449 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12449 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163904156098 + 0.011885274193 + (0.008567209136 : ℝ) *
        (1 + 2 * (0.284211610279 + 0.011885274193) / (0.560491988464 * 111.575086824971))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12449]

end BstLean.Part269.N12449

/-! The original eight local profiles supply actual 12449 moment certificates. -/
namespace BstLean.Part269.N12449
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12449 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12449 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12449 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053451160735 ∧
    0 ≤ bN 12449 BstLean.Part154.csC (groupTheta g) ∧ bN 12449 BstLean.Part154.csC (groupTheta g) ≤ 0.001409193430 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12449 12449 0.011
      (momentAllowance 12449 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12449 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12449 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12449 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12449 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12449 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231195070742 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12449 0.011
      (momentAllowance 12449 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12449 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12449
/-! The actual computed-centre upper energy formula at 12449. -/
namespace BstLean.Part269.N12449
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12449

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12449
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12449)
open BstLean.Part268 (cell12449)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086259535436
  | 2 => 0.087217300358
  | 3 => 0.088175534431
  | 4 => 0.089136181526
  | 5 => 0.090101573616
  | 6 => 0.091074485861
  | 7 => 0.092058196404
  | 8 => 0.093056550870
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12449 12449 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12449 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004185346396 + 0.003369149079 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S3.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S3.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12449

/-! Actual upper energy certificates on all 43 source endpoints at 12449. -/
namespace BstLean.Part269.N12449
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12449)
open BstLean.Part268 (cell12449)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12449 (gMinus 12449) (1 - (cell12449 i).lower) ≤ 1 ∧
    energyUpper 12449 (gMinus 12449) (BstLean.Part211.gPlus 12449)
      (finiteEnergy 12449 12449 0.011) (1 - (cell12449 i).lower) ≤
      (cell12449 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨10,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨11,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨12,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨13,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨14,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨15,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨16,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨17,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨18,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨19,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨20,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨21,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨22,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨23,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨24,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨25,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨26,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨27,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨28,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨29,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨30,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨31,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨32,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨33,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨34,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨35,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨36,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨37,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨38,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨39,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨40,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨41,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨42,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨43,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨44,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨45,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨46,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨47,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨48,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨49,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨50,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨51,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12449) (by norm_num)
        (q := 1 - (cell12449 ⟨52,by decide⟩).lower)
        (by norm_num [cell12449]) (by norm_num [cell12449])
      exact ⟨E.1,E.2.trans (by norm_num [cell12449])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12449

/-! Source-cell containment and simple scalar guards at 12449. -/
namespace BstLean.Part269.N12449
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12449)
open BstLean.Part268 (cell12449)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12449 ⟨10,by decide⟩).lower ∧ (cell12449 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12449 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12449 ⟨11,by decide⟩).lower ∧ (cell12449 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12449 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12449 ⟨12,by decide⟩).lower ∧ (cell12449 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12449 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12449 ⟨13,by decide⟩).lower ∧ (cell12449 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12449 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12449 ⟨14,by decide⟩).lower ∧ (cell12449 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12449 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12449 ⟨15,by decide⟩).lower ∧ (cell12449 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12449 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12449 ⟨16,by decide⟩).lower ∧ (cell12449 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12449 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12449 ⟨17,by decide⟩).lower ∧ (cell12449 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12449 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12449 ⟨18,by decide⟩).lower ∧ (cell12449 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12449 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12449 ⟨19,by decide⟩).lower ∧ (cell12449 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12449 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12449 ⟨20,by decide⟩).lower ∧ (cell12449 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12449 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12449 ⟨21,by decide⟩).lower ∧ (cell12449 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12449 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12449 ⟨22,by decide⟩).lower ∧ (cell12449 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12449 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12449 ⟨23,by decide⟩).lower ∧ (cell12449 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12449 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12449 ⟨24,by decide⟩).lower ∧ (cell12449 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12449 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12449 ⟨25,by decide⟩).lower ∧ (cell12449 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12449 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12449 ⟨26,by decide⟩).lower ∧ (cell12449 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12449 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12449 ⟨27,by decide⟩).lower ∧ (cell12449 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12449 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12449 ⟨28,by decide⟩).lower ∧ (cell12449 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12449 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12449 ⟨29,by decide⟩).lower ∧ (cell12449 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12449 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12449 ⟨30,by decide⟩).lower ∧ (cell12449 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12449 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12449 ⟨31,by decide⟩).lower ∧ (cell12449 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12449 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12449 ⟨32,by decide⟩).lower ∧ (cell12449 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12449 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12449 ⟨33,by decide⟩).lower ∧ (cell12449 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12449 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12449 ⟨34,by decide⟩).lower ∧ (cell12449 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12449 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12449 ⟨35,by decide⟩).lower ∧ (cell12449 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12449 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12449 ⟨36,by decide⟩).lower ∧ (cell12449 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12449 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12449 ⟨37,by decide⟩).lower ∧ (cell12449 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12449 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12449 ⟨38,by decide⟩).lower ∧ (cell12449 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12449 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12449 ⟨39,by decide⟩).lower ∧ (cell12449 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12449 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12449 ⟨40,by decide⟩).lower ∧ (cell12449 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12449 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12449 ⟨41,by decide⟩).lower ∧ (cell12449 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12449 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12449 ⟨42,by decide⟩).lower ∧ (cell12449 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12449 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12449 ⟨43,by decide⟩).lower ∧ (cell12449 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12449 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12449 ⟨44,by decide⟩).lower ∧ (cell12449 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12449 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12449 ⟨45,by decide⟩).lower ∧ (cell12449 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12449 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12449 ⟨46,by decide⟩).lower ∧ (cell12449 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12449 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12449 ⟨47,by decide⟩).lower ∧ (cell12449 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12449 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12449 ⟨48,by decide⟩).lower ∧ (cell12449 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12449 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12449 ⟨49,by decide⟩).lower ∧ (cell12449 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12449 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12449 ⟨50,by decide⟩).lower ∧ (cell12449 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12449 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12449 ⟨51,by decide⟩).lower ∧ (cell12449 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12449 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12449 ⟨52,by decide⟩).lower ∧ (cell12449 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12449 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12449 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12449 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12449,cell12449,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12449 i).lower ∧
    (cell12449 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12449 i).upper ≤ (0.532 : ℝ) ∧
    (cell12449 i).centre ≤ (0.1 : ℝ) ∧ (cell12449 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12449 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12449 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12449

/-! The local source numeric instances at 12449 have no network premises. -/
namespace BstLean.Part269.N12449
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12449)
open BstLean.Part268 (cell12449)

noncomputable def sourceNumerics12449 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12449 (cell12449 i)
      scalarRow12449.M scalarRow12449.H scalarRow12449.xi := by
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
    energy_allowance := scalarRow12449.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12449]
    centre_nonneg := (scalarRow12449.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12449])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12449