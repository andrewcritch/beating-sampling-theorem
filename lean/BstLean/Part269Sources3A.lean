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
/-! Actual 12425 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12425
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12425 ≤ (1.036206835911 : ℝ) := by
  have hr : (111.467484048039 : ℝ) ≤ √(12425 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.467484048039 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12425 12425 (11 / 1000) ≤
    (0.008575479375 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12425) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.467484048039 : ℝ) ≤ √(12425 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12425)
  have hdiv : K / √(12425 : ℝ) ≤ K / 111.467484048039 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.467484048039 ≤ (0.008575479375 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12425.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12425 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12425 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12425 := gPlus_lower 12425
end BstLean.Part269.N12425

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12425
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036206835910 : ℝ) ≤ wn 12425 := by
  have hn : √(12425 : ℝ) ≤ 111.467484048040 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12425 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.467484048040 ≤ 2 / √(12425 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257554526 : ℝ) ≤ rhoBar 12425 BstLean.Part154.csC ∧
    rhoBar 12425 BstLean.Part154.csC ≤ 0.000257554925 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036206835910 : ℝ) / (1.295212 * 12425) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036206835911 : ℝ) / (1.29521 * 12425) := by gcongr
      _ ≤ (0.000257554925 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12425 BstLean.Part154.csC) ≤ 0.001030286035 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12425 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12425 BstLean.Part154.csC) (piBar (rhoBar 12425 BstLean.Part154.csC)) ≤ 0.000196722395 ∧
    cc1 (rhoBar 12425 BstLean.Part154.csC) (piBar (rhoBar 12425 BstLean.Part154.csC)) ≤ 0.000125175724 ∧
    cc2 (rhoBar 12425 BstLean.Part154.csC) ≤ 0.000072665415 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12425 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12425 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12425 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12425 BstLean.Part154.csC * nuR (rhoBar 12425 BstLean.Part154.csC)) ≤ 0.000515126434 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257554925 : ℝ) * 0.001030286035 := by gcongr
      _ ≤ (0.000515126434 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12425 BstLean.Part154.csC) * nuR (rhoBar 12425 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001030286035 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12425 BstLean.Part154.csC) * rhoBar 12425 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257554925 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257554925 / 2 + 0.399 * 0.001030286035 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196722395 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515126434 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125175724 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257554925 / 1.414213562 := by gcongr
      _ ≤ (0.000072665415 : ℝ) := by norm_num

end BstLean.Part269.N12425

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12425
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12425 BstLean.Part154.csC) (piBar (rhoBar 12425 BstLean.Part154.csC)) ≤ 1.67125E-7 := by
  have hr0 : 0 ≤ rhoBar 12425 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12425 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12425 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12425 BstLean.Part154.csC) (piBar (rhoBar 12425 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12425 BstLean.Part154.csC) (piBar (rhoBar 12425 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12425 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196722395 : ℝ) ^ 2 + 0.000125175724 ^ 2 + 3 * 0.000072665415 ^ 2 +
        2 * 0.797885 * 0.000196722395 * 0.000125175724 + 2 * 0.000196722395 * 0.000072665415 +
        4 * 0.797885 * 0.000125175724 * 0.000072665415 := by gcongr
    _ ≤ (1.67125E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12425 BstLean.Part154.csC Θ ≤ 0.002689544155 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12425 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12425 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12425 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12425 BstLean.Part154.csC) (piBar (rhoBar 12425 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12425 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036206835911 * 1.67125E-7 / (0.000257554526 : ℝ) := by gcongr
    _ ≤ 0.002689544155 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12425 BstLean.Part154.csC Θ ≤ 0.002985346396 + 0.000679604924 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12425 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12425 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12425 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036206835911 : ℝ) * ((2 * Θ * 0.000257554925 +
        (6863 / 10000) * 0.000257554925 * 12425 * 0.001030286035) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002985346396 + 0.000679604924 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12425 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12425 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12425 0.011 Θ ∧ gammaRatio 12425 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12425 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036206835911 : ℝ) * 0.525 / ((1 - 0.011) * 12425) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12425 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12425 0.011 Θ) :=
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
    badAllowance 12425 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12425 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12425 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12425 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12425 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12425 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12425 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12425 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12425 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12425 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12425 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036206835911 : ℝ) * 12425 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12425 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004185346396 + 0.003369149079 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12425

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12425
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12425 BstLean.Part154.csC) (piBar (rhoBar 12425 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12425 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12425 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12425 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12425 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12425 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12425 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12425 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12425 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12425 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12425 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12425 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12425 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12425 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12425 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053068278929 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12425) ≤ 0.010713775334 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12425 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036206835911)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010713775334 + 2 * 0.737676 / 12425) := by gcongr
    _ ≤ (0.053068278929 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12425 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12425

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12425
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490856724 : ℝ) ≤ plow 12425 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12425) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053460749663)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412010682) : eMP 12425 0.011 xi bn ≤ 0.001215316527 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12425 : ℝ) * (1 - 0.011))) ≤ 0.000600824463 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001412010682 / (12425 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000600824463 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000600824463 : ℝ) + 3.141593 * 0.053460749663 / (12425 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001215316527 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053460749663)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412010682) : PiBarMP 12425 12 0.011 xi bn ≤ 0.163046877424 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12425 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037576730593 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.852717603133 : ℝ) ≤ √((12425 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.467484048039 : ℝ) ≤ √(12425 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12425) ≤ 0.124990784369 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037576730593 + 0.053460749663 * 1.772454 / (2 * (110.852717603133 : ℝ))) * (1 + 0.001215316527) +
        8 / (12425 * 111.467484048039) + 0.124990784369 := by gcongr
    _ ≤ (0.163046877424 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053460749663)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412010682) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284284086484) :
    parallelOracle 12425 0.011 xi bn cd ≤ 0.164064612597 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12425 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12425 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490856724 : ℝ) ≤ plow 12425 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.467484048039 : ℝ) ≤ √(12425 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284284086484 : ℝ) / (2 * 0.560490856724 * 111.467484048039)) * 0.163046877424 +
        0.284284086484 ^ 2 / (2 * 0.560490856724 * 111.467484048039) := by gcongr
    _ ≤ (0.164064612597 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053460749663) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412010682)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284284086484) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12425 12425 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490856724 : ℝ) ≤ plow 12425 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.467484048039 : ℝ) ≤ √(12425 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12425 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12425 Θ 1.22 ≤ 0.011896747391 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.467484048039 := by gcongr <;> linarith
      _ ≤ (0.011896747391 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12425 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12425 12425 0.011 ≤ 0.008575479375 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12425 12425 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12425 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12425 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12425 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12425 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164064612597 + 0.011896747391 + (0.008575479375 : ℝ) *
        (1 + 2 * (0.284284086484 + 0.011896747391) / (0.560490856724 * 111.467484048039))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12425]

end BstLean.Part269.N12425

/-! The original eight local profiles supply actual 12425 moment certificates. -/
namespace BstLean.Part269.N12425
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12425 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12425 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12425 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053460749663 ∧
    0 ≤ bN 12425 BstLean.Part154.csC (groupTheta g) ∧ bN 12425 BstLean.Part154.csC (groupTheta g) ≤ 0.001412010682 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12425 12425 0.011
      (momentAllowance 12425 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12425 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12425 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12425 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12425 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12425 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231215807555 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12425 0.011
      (momentAllowance 12425 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12425 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12425
/-! The actual computed-centre upper energy formula at 12425. -/
namespace BstLean.Part269.N12425
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12425

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12425
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12425)
open BstLean.Part268 (cell12425)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086337393367
  | 2 => 0.087296779188
  | 3 => 0.088256900210
  | 4 => 0.089219759171
  | 5 => 0.090187756882
  | 6 => 0.091163748467
  | 7 => 0.092151104380
  | 8 => 0.093153776150
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12425 12425 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12425 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12425

/-! Actual upper energy certificates on all 43 source endpoints at 12425. -/
namespace BstLean.Part269.N12425
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12425)
open BstLean.Part268 (cell12425)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12425 (gMinus 12425) (1 - (cell12425 i).lower) ≤ 1 ∧
    energyUpper 12425 (gMinus 12425) (BstLean.Part211.gPlus 12425)
      (finiteEnergy 12425 12425 0.011) (1 - (cell12425 i).lower) ≤
      (cell12425 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨10,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨11,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨12,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨13,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨14,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨15,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨16,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨17,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨18,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨19,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨20,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨21,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨22,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨23,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨24,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨25,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨26,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨27,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨28,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨29,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨30,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨31,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨32,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨33,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨34,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨35,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨36,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨37,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨38,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨39,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨40,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨41,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨42,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨43,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨44,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨45,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨46,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨47,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨48,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨49,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨50,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨51,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12425) (by norm_num)
        (q := 1 - (cell12425 ⟨52,by decide⟩).lower)
        (by norm_num [cell12425]) (by norm_num [cell12425])
      exact ⟨E.1,E.2.trans (by norm_num [cell12425])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12425

/-! Source-cell containment and simple scalar guards at 12425. -/
namespace BstLean.Part269.N12425
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12425)
open BstLean.Part268 (cell12425)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12425 ⟨10,by decide⟩).lower ∧ (cell12425 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12425 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12425 ⟨11,by decide⟩).lower ∧ (cell12425 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12425 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12425 ⟨12,by decide⟩).lower ∧ (cell12425 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12425 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12425 ⟨13,by decide⟩).lower ∧ (cell12425 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12425 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12425 ⟨14,by decide⟩).lower ∧ (cell12425 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12425 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12425 ⟨15,by decide⟩).lower ∧ (cell12425 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12425 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12425 ⟨16,by decide⟩).lower ∧ (cell12425 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12425 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12425 ⟨17,by decide⟩).lower ∧ (cell12425 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12425 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12425 ⟨18,by decide⟩).lower ∧ (cell12425 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12425 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12425 ⟨19,by decide⟩).lower ∧ (cell12425 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12425 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12425 ⟨20,by decide⟩).lower ∧ (cell12425 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12425 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12425 ⟨21,by decide⟩).lower ∧ (cell12425 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12425 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12425 ⟨22,by decide⟩).lower ∧ (cell12425 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12425 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12425 ⟨23,by decide⟩).lower ∧ (cell12425 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12425 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12425 ⟨24,by decide⟩).lower ∧ (cell12425 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12425 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12425 ⟨25,by decide⟩).lower ∧ (cell12425 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12425 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12425 ⟨26,by decide⟩).lower ∧ (cell12425 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12425 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12425 ⟨27,by decide⟩).lower ∧ (cell12425 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12425 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12425 ⟨28,by decide⟩).lower ∧ (cell12425 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12425 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12425 ⟨29,by decide⟩).lower ∧ (cell12425 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12425 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12425 ⟨30,by decide⟩).lower ∧ (cell12425 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12425 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12425 ⟨31,by decide⟩).lower ∧ (cell12425 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12425 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12425 ⟨32,by decide⟩).lower ∧ (cell12425 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12425 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12425 ⟨33,by decide⟩).lower ∧ (cell12425 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12425 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12425 ⟨34,by decide⟩).lower ∧ (cell12425 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12425 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12425 ⟨35,by decide⟩).lower ∧ (cell12425 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12425 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12425 ⟨36,by decide⟩).lower ∧ (cell12425 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12425 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12425 ⟨37,by decide⟩).lower ∧ (cell12425 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12425 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12425 ⟨38,by decide⟩).lower ∧ (cell12425 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12425 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12425 ⟨39,by decide⟩).lower ∧ (cell12425 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12425 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12425 ⟨40,by decide⟩).lower ∧ (cell12425 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12425 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12425 ⟨41,by decide⟩).lower ∧ (cell12425 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12425 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12425 ⟨42,by decide⟩).lower ∧ (cell12425 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12425 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12425 ⟨43,by decide⟩).lower ∧ (cell12425 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12425 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12425 ⟨44,by decide⟩).lower ∧ (cell12425 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12425 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12425 ⟨45,by decide⟩).lower ∧ (cell12425 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12425 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12425 ⟨46,by decide⟩).lower ∧ (cell12425 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12425 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12425 ⟨47,by decide⟩).lower ∧ (cell12425 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12425 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12425 ⟨48,by decide⟩).lower ∧ (cell12425 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12425 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12425 ⟨49,by decide⟩).lower ∧ (cell12425 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12425 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12425 ⟨50,by decide⟩).lower ∧ (cell12425 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12425 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12425 ⟨51,by decide⟩).lower ∧ (cell12425 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12425 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12425 ⟨52,by decide⟩).lower ∧ (cell12425 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12425 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12425 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12425 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12425,cell12425,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12425 i).lower ∧
    (cell12425 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12425 i).upper ≤ (0.532 : ℝ) ∧
    (cell12425 i).centre ≤ (0.1 : ℝ) ∧ (cell12425 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12425 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12425 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12425

/-! The local source numeric instances at 12425 have no network premises. -/
namespace BstLean.Part269.N12425
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12425)
open BstLean.Part268 (cell12425)

noncomputable def sourceNumerics12425 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12425 (cell12425 i)
      scalarRow12425.M scalarRow12425.H scalarRow12425.xi := by
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
    energy_allowance := scalarRow12425.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12425]
    centre_nonneg := (scalarRow12425.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12425])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12425
/-! Actual 12426 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12426
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12426 ≤ (1.036205366030 : ℝ) := by
  have hr : (111.471969570829 : ℝ) ≤ √(12426 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.471969570829 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12426 12426 (11 / 1000) ≤
    (0.008575134304 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12426) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.471969570829 : ℝ) ≤ √(12426 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12426)
  have hdiv : K / √(12426 : ℝ) ≤ K / 111.471969570829 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.471969570829 ≤ (0.008575134304 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12426.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12426 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12426 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12426 := gPlus_lower 12426
end BstLean.Part269.N12426

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12426
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036205366029 : ℝ) ≤ wn 12426 := by
  have hn : √(12426 : ℝ) ≤ 111.471969570830 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12426 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.471969570830 ≤ 2 / √(12426 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257533434 : ℝ) ≤ rhoBar 12426 BstLean.Part154.csC ∧
    rhoBar 12426 BstLean.Part154.csC ≤ 0.000257533833 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036205366029 : ℝ) / (1.295212 * 12426) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036205366030 : ℝ) / (1.29521 * 12426) := by gcongr
      _ ≤ (0.000257533833 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12426 BstLean.Part154.csC) ≤ 0.001030201656 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12426 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12426 BstLean.Part154.csC) (piBar (rhoBar 12426 BstLean.Part154.csC)) ≤ 0.000196706284 ∧
    cc1 (rhoBar 12426 BstLean.Part154.csC) (piBar (rhoBar 12426 BstLean.Part154.csC)) ≤ 0.000125165473 ∧
    cc2 (rhoBar 12426 BstLean.Part154.csC) ≤ 0.000072659464 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12426 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12426 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12426 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12426 BstLean.Part154.csC * nuR (rhoBar 12426 BstLean.Part154.csC)) ≤ 0.000515084247 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257533833 : ℝ) * 0.001030201656 := by gcongr
      _ ≤ (0.000515084247 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12426 BstLean.Part154.csC) * nuR (rhoBar 12426 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001030201656 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12426 BstLean.Part154.csC) * rhoBar 12426 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257533833 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257533833 / 2 + 0.399 * 0.001030201656 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196706284 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515084247 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125165473 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257533833 / 1.414213562 := by gcongr
      _ ≤ (0.000072659464 : ℝ) := by norm_num

end BstLean.Part269.N12426

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12426
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12426 BstLean.Part154.csC) (piBar (rhoBar 12426 BstLean.Part154.csC)) ≤ 1.67098E-7 := by
  have hr0 : 0 ≤ rhoBar 12426 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12426 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12426 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12426 BstLean.Part154.csC) (piBar (rhoBar 12426 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12426 BstLean.Part154.csC) (piBar (rhoBar 12426 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12426 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196706284 : ℝ) ^ 2 + 0.000125165473 ^ 2 + 3 * 0.000072659464 ^ 2 +
        2 * 0.797885 * 0.000196706284 * 0.000125165473 + 2 * 0.000196706284 * 0.000072659464 +
        4 * 0.797885 * 0.000125165473 * 0.000072659464 := by gcongr
    _ ≤ (1.67098E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12426 BstLean.Part154.csC Θ ≤ 0.002689326067 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12426 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12426 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12426 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12426 BstLean.Part154.csC) (piBar (rhoBar 12426 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12426 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036205366030 * 1.67098E-7 / (0.000257533434 : ℝ) := by gcongr
    _ ≤ 0.002689326067 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12426 BstLean.Part154.csC Θ ≤ 0.002985093437 + 0.000679548305 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12426 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12426 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12426 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036205366030 : ℝ) * ((2 * Θ * 0.000257533833 +
        (6863 / 10000) * 0.000257533833 * 12426 * 0.001030201656) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002985093437 + 0.000679548305 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12426 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12426 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12426 0.011 Θ ∧ gammaRatio 12426 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12426 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036205366030 : ℝ) * 0.525 / ((1 - 0.011) * 12426) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12426 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12426 0.011 Θ) :=
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
    badAllowance 12426 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12426 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12426 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12426 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12426 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12426 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12426 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12426 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12426 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12426 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12426 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036205366030 : ℝ) * 12426 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12426 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004185093437 + 0.003368874372 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12426

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12426
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12426 BstLean.Part154.csC) (piBar (rhoBar 12426 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12426 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12426 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12426 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12426 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12426 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12426 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12426 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12426 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12426 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12426 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12426 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12426 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12426 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12426 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053066120106 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12426) ≤ 0.010713344222 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12426 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036205366030)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010713344222 + 2 * 0.737676 / 12426) := by gcongr
    _ ≤ (0.053066120106 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12426 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12426

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12426
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490903967 : ℝ) ≤ plow 12426 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12426) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053460352483)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411896186) : eMP 12426 0.011 xi bn ≤ 0.001215218256 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12426 : ℝ) * (1 - 0.011))) ≤ 0.000600775928 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001411896186 / (12426 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000600775928 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000600775928 : ℝ) + 3.141593 * 0.053460352483 / (12426 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001215218256 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053460352483)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411896186) : PiBarMP 12426 12 0.011 xi bn ≤ 0.163040297709 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12426 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037575207066 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.857178387328 : ℝ) ≤ √((12426 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.471969570829 : ℝ) ≤ √(12426 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12426) ≤ 0.124985754862 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037575207066 + 0.053460352483 * 1.772454 / (2 * (110.857178387328 : ℝ))) * (1 + 0.001215218256) +
        8 / (12426 * 111.471969570829) + 0.124985754862 := by gcongr
    _ ≤ (0.163040297709 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053460352483)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411896186) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284281068765) :
    parallelOracle 12426 0.011 xi bn cd ≤ 0.164057959206 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12426 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12426 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490903967 : ℝ) ≤ plow 12426 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.471969570829 : ℝ) ≤ √(12426 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284281068765 : ℝ) / (2 * 0.560490903967 * 111.471969570829)) * 0.163040297709 +
        0.284281068765 ^ 2 / (2 * 0.560490903967 * 111.471969570829) := by gcongr
    _ ≤ (0.164057959206 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053460352483) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411896186)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284281068765) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12426 12426 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490903967 : ℝ) ≤ plow 12426 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.471969570829 : ℝ) ≤ √(12426 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12426 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12426 Θ 1.22 ≤ 0.011896268678 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.471969570829 := by gcongr <;> linarith
      _ ≤ (0.011896268678 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12426 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12426 12426 0.011 ≤ 0.008575134304 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12426 12426 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12426 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12426 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12426 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12426 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164057959206 + 0.011896268678 + (0.008575134304 : ℝ) *
        (1 + 2 * (0.284281068765 + 0.011896268678) / (0.560490903967 * 111.471969570829))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12426]

end BstLean.Part269.N12426

/-! The original eight local profiles supply actual 12426 moment certificates. -/
namespace BstLean.Part269.N12426
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12426 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12426 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12426 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053460352483 ∧
    0 ≤ bN 12426 BstLean.Part154.csC (groupTheta g) ∧ bN 12426 BstLean.Part154.csC (groupTheta g) ≤ 0.001411896186 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12426 12426 0.011
      (momentAllowance 12426 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12426 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12426 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12426 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12426 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12426 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231214948659 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12426 0.011
      (momentAllowance 12426 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12426 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12426
/-! The actual computed-centre upper energy formula at 12426. -/
namespace BstLean.Part269.N12426
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12426

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12426
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12426)
open BstLean.Part268 (cell12426)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086334132799
  | 2 => 0.087293450358
  | 3 => 0.088253491863
  | 4 => 0.089216257567
  | 5 => 0.090184145374
  | 6 => 0.091160007034
  | 7 => 0.092147209105
  | 8 => 0.093149698649
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12426 12426 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12426 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12426

/-! Actual upper energy certificates on all 43 source endpoints at 12426. -/
namespace BstLean.Part269.N12426
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12426)
open BstLean.Part268 (cell12426)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12426 (gMinus 12426) (1 - (cell12426 i).lower) ≤ 1 ∧
    energyUpper 12426 (gMinus 12426) (BstLean.Part211.gPlus 12426)
      (finiteEnergy 12426 12426 0.011) (1 - (cell12426 i).lower) ≤
      (cell12426 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨10,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨11,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨12,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨13,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨14,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨15,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨16,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨17,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨18,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨19,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨20,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨21,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨22,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨23,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨24,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨25,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨26,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨27,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨28,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨29,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨30,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨31,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨32,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨33,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨34,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨35,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨36,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨37,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨38,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨39,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨40,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨41,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨42,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨43,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨44,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨45,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨46,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨47,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨48,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨49,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨50,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨51,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12426) (by norm_num)
        (q := 1 - (cell12426 ⟨52,by decide⟩).lower)
        (by norm_num [cell12426]) (by norm_num [cell12426])
      exact ⟨E.1,E.2.trans (by norm_num [cell12426])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12426

/-! Source-cell containment and simple scalar guards at 12426. -/
namespace BstLean.Part269.N12426
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12426)
open BstLean.Part268 (cell12426)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12426 ⟨10,by decide⟩).lower ∧ (cell12426 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12426 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12426 ⟨11,by decide⟩).lower ∧ (cell12426 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12426 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12426 ⟨12,by decide⟩).lower ∧ (cell12426 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12426 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12426 ⟨13,by decide⟩).lower ∧ (cell12426 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12426 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12426 ⟨14,by decide⟩).lower ∧ (cell12426 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12426 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12426 ⟨15,by decide⟩).lower ∧ (cell12426 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12426 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12426 ⟨16,by decide⟩).lower ∧ (cell12426 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12426 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12426 ⟨17,by decide⟩).lower ∧ (cell12426 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12426 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12426 ⟨18,by decide⟩).lower ∧ (cell12426 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12426 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12426 ⟨19,by decide⟩).lower ∧ (cell12426 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12426 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12426 ⟨20,by decide⟩).lower ∧ (cell12426 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12426 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12426 ⟨21,by decide⟩).lower ∧ (cell12426 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12426 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12426 ⟨22,by decide⟩).lower ∧ (cell12426 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12426 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12426 ⟨23,by decide⟩).lower ∧ (cell12426 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12426 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12426 ⟨24,by decide⟩).lower ∧ (cell12426 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12426 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12426 ⟨25,by decide⟩).lower ∧ (cell12426 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12426 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12426 ⟨26,by decide⟩).lower ∧ (cell12426 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12426 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12426 ⟨27,by decide⟩).lower ∧ (cell12426 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12426 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12426 ⟨28,by decide⟩).lower ∧ (cell12426 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12426 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12426 ⟨29,by decide⟩).lower ∧ (cell12426 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12426 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12426 ⟨30,by decide⟩).lower ∧ (cell12426 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12426 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12426 ⟨31,by decide⟩).lower ∧ (cell12426 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12426 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12426 ⟨32,by decide⟩).lower ∧ (cell12426 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12426 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12426 ⟨33,by decide⟩).lower ∧ (cell12426 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12426 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12426 ⟨34,by decide⟩).lower ∧ (cell12426 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12426 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12426 ⟨35,by decide⟩).lower ∧ (cell12426 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12426 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12426 ⟨36,by decide⟩).lower ∧ (cell12426 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12426 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12426 ⟨37,by decide⟩).lower ∧ (cell12426 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12426 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12426 ⟨38,by decide⟩).lower ∧ (cell12426 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12426 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12426 ⟨39,by decide⟩).lower ∧ (cell12426 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12426 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12426 ⟨40,by decide⟩).lower ∧ (cell12426 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12426 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12426 ⟨41,by decide⟩).lower ∧ (cell12426 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12426 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12426 ⟨42,by decide⟩).lower ∧ (cell12426 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12426 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12426 ⟨43,by decide⟩).lower ∧ (cell12426 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12426 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12426 ⟨44,by decide⟩).lower ∧ (cell12426 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12426 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12426 ⟨45,by decide⟩).lower ∧ (cell12426 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12426 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12426 ⟨46,by decide⟩).lower ∧ (cell12426 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12426 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12426 ⟨47,by decide⟩).lower ∧ (cell12426 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12426 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12426 ⟨48,by decide⟩).lower ∧ (cell12426 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12426 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12426 ⟨49,by decide⟩).lower ∧ (cell12426 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12426 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12426 ⟨50,by decide⟩).lower ∧ (cell12426 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12426 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12426 ⟨51,by decide⟩).lower ∧ (cell12426 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12426 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12426 ⟨52,by decide⟩).lower ∧ (cell12426 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12426 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12426 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12426 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12426,cell12426,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12426 i).lower ∧
    (cell12426 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12426 i).upper ≤ (0.532 : ℝ) ∧
    (cell12426 i).centre ≤ (0.1 : ℝ) ∧ (cell12426 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12426 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12426 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12426

/-! The local source numeric instances at 12426 have no network premises. -/
namespace BstLean.Part269.N12426
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12426)
open BstLean.Part268 (cell12426)

noncomputable def sourceNumerics12426 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12426 (cell12426 i)
      scalarRow12426.M scalarRow12426.H scalarRow12426.xi := by
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
    energy_allowance := scalarRow12426.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12426]
    centre_nonneg := (scalarRow12426.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12426])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12426
/-! Actual 12427 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12427
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12427 ≤ (1.036203896327 : ℝ) := by
  have hr : (111.476454913134 : ℝ) ≤ √(12427 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.476454913134 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12427 12427 (11 / 1000) ≤
    (0.008574789274 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12427) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.476454913134 : ℝ) ≤ √(12427 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12427)
  have hdiv : K / √(12427 : ℝ) ≤ K / 111.476454913134 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.476454913134 ≤ (0.008574789274 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12427.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12427 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12427 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12427 := gPlus_lower 12427
end BstLean.Part269.N12427

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12427
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036203896326 : ℝ) ≤ wn 12427 := by
  have hn : √(12427 : ℝ) ≤ 111.476454913135 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12427 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.476454913135 ≤ 2 / √(12427 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257512345 : ℝ) ≤ rhoBar 12427 BstLean.Part154.csC ∧
    rhoBar 12427 BstLean.Part154.csC ≤ 0.000257512744 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036203896326 : ℝ) / (1.295212 * 12427) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036203896327 : ℝ) / (1.29521 * 12427) := by gcongr
      _ ≤ (0.000257512744 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12427 BstLean.Part154.csC) ≤ 0.001030117289 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12427 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12427 BstLean.Part154.csC) (piBar (rhoBar 12427 BstLean.Part154.csC)) ≤ 0.000196690176 ∧
    cc1 (rhoBar 12427 BstLean.Part154.csC) (piBar (rhoBar 12427 BstLean.Part154.csC)) ≤ 0.000125155223 ∧
    cc2 (rhoBar 12427 BstLean.Part154.csC) ≤ 0.000072653515 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12427 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12427 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12427 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12427 BstLean.Part154.csC * nuR (rhoBar 12427 BstLean.Part154.csC)) ≤ 0.000515042066 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257512744 : ℝ) * 0.001030117289 := by gcongr
      _ ≤ (0.000515042066 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12427 BstLean.Part154.csC) * nuR (rhoBar 12427 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001030117289 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12427 BstLean.Part154.csC) * rhoBar 12427 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257512744 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257512744 / 2 + 0.399 * 0.001030117289 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196690176 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515042066 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125155223 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257512744 / 1.414213562 := by gcongr
      _ ≤ (0.000072653515 : ℝ) := by norm_num

end BstLean.Part269.N12427

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12427
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12427 BstLean.Part154.csC) (piBar (rhoBar 12427 BstLean.Part154.csC)) ≤ 1.67071E-7 := by
  have hr0 : 0 ≤ rhoBar 12427 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12427 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12427 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12427 BstLean.Part154.csC) (piBar (rhoBar 12427 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12427 BstLean.Part154.csC) (piBar (rhoBar 12427 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12427 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196690176 : ℝ) ^ 2 + 0.000125155223 ^ 2 + 3 * 0.000072653515 ^ 2 +
        2 * 0.797885 * 0.000196690176 * 0.000125155223 + 2 * 0.000196690176 * 0.000072653515 +
        4 * 0.797885 * 0.000125155223 * 0.000072653515 := by gcongr
    _ ≤ (1.67071E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12427 BstLean.Part154.csC Θ ≤ 0.002689107914 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12427 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12427 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12427 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12427 BstLean.Part154.csC) (piBar (rhoBar 12427 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12427 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036203896327 * 1.67071E-7 / (0.000257512345 : ℝ) := by gcongr
    _ ≤ 0.002689107914 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12427 BstLean.Part154.csC Θ ≤ 0.002984840509 + 0.000679491694 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12427 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12427 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12427 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036203896327 : ℝ) * ((2 * Θ * 0.000257512744 +
        (6863 / 10000) * 0.000257512744 * 12427 * 0.001030117289) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002984840509 + 0.000679491694 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12427 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12427 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12427 0.011 Θ ∧ gammaRatio 12427 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12427 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036203896327 : ℝ) * 0.525 / ((1 - 0.011) * 12427) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12427 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12427 0.011 Θ) :=
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
    badAllowance 12427 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12427 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12427 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12427 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12427 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12427 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12427 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12427 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12427 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12427 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12427 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036203896327 : ℝ) * 12427 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12427 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004184840509 + 0.003368599608 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12427

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12427
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12427 BstLean.Part154.csC) (piBar (rhoBar 12427 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12427 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12427 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12427 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12427 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12427 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12427 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12427 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12427 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12427 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12427 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12427 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12427 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12427 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12427 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053063961545 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12427) ≤ 0.010712913162 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12427 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036203896327)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010712913162 + 2 * 0.737676 / 12427) := by gcongr
    _ ≤ (0.053063961545 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12427 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12427

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12427
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490951203 : ℝ) ≤ plow 12427 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12427) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053459955304)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411781655) : eMP 12427 0.011 xi bn ≤ 0.001215119974 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12427 : ℝ) * (1 - 0.011))) ≤ 0.000600727388 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001411781655 / (12427 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000600727388 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000600727388 : ℝ) + 3.141593 * 0.053459955304 / (12427 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001215119974 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053459955304)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411781655) : PiBarMP 12427 12 0.011 xi bn ≤ 0.163033718075 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12427 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037573683011 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.861638992033 : ℝ) ≤ √((12427 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.476454913134 : ℝ) ≤ √(12427 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12427) ≤ 0.124980725963 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037573683011 + 0.053459955304 * 1.772454 / (2 * (110.861638992033 : ℝ))) * (1 + 0.001215119974) +
        8 / (12427 * 111.476454913134) + 0.124980725963 := by gcongr
    _ ≤ (0.163033718075 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053459955304)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411781655) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284278051306) :
    parallelOracle 12427 0.011 xi bn cd ≤ 0.164051305906 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12427 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12427 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490951203 : ℝ) ≤ plow 12427 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.476454913134 : ℝ) ≤ √(12427 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284278051306 : ℝ) / (2 * 0.560490951203 * 111.476454913134)) * 0.163033718075 +
        0.284278051306 ^ 2 / (2 * 0.560490951203 * 111.476454913134) := by gcongr
    _ ≤ (0.164051305906 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053459955304) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411781655)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284278051306) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12427 12427 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490951203 : ℝ) ≤ plow 12427 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.476454913134 : ℝ) ≤ √(12427 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12427 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12427 Θ 1.22 ≤ 0.011895790022 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.476454913134 := by gcongr <;> linarith
      _ ≤ (0.011895790022 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12427 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12427 12427 0.011 ≤ 0.008574789274 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12427 12427 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12427 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12427 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12427 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12427 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164051305906 + 0.011895790022 + (0.008574789274 : ℝ) *
        (1 + 2 * (0.284278051306 + 0.011895790022) / (0.560490951203 * 111.476454913134))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12427]

end BstLean.Part269.N12427

/-! The original eight local profiles supply actual 12427 moment certificates. -/
namespace BstLean.Part269.N12427
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12427 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12427 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12427 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053459955304 ∧
    0 ≤ bN 12427 BstLean.Part154.csC (groupTheta g) ∧ bN 12427 BstLean.Part154.csC (groupTheta g) ≤ 0.001411781655 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12427 12427 0.011
      (momentAllowance 12427 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12427 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12427 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12427 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12427 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12427 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231214089761 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12427 0.011
      (momentAllowance 12427 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12427 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12427
/-! The actual computed-centre upper energy formula at 12427. -/
namespace BstLean.Part269.N12427
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12427

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12427
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12427)
open BstLean.Part268 (cell12427)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086330873676
  | 2 => 0.087290123036
  | 3 => 0.088250085103
  | 4 => 0.089212757646
  | 5 => 0.090180535667
  | 6 => 0.091156267544
  | 7 => 0.092143315944
  | 8 => 0.093145623467
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12427 12427 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12427 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12427

/-! Actual upper energy certificates on all 43 source endpoints at 12427. -/
namespace BstLean.Part269.N12427
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12427)
open BstLean.Part268 (cell12427)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12427 (gMinus 12427) (1 - (cell12427 i).lower) ≤ 1 ∧
    energyUpper 12427 (gMinus 12427) (BstLean.Part211.gPlus 12427)
      (finiteEnergy 12427 12427 0.011) (1 - (cell12427 i).lower) ≤
      (cell12427 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨10,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨11,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨12,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨13,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨14,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨15,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨16,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨17,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨18,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨19,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨20,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨21,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨22,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨23,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨24,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨25,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨26,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨27,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨28,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨29,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨30,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨31,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨32,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨33,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨34,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨35,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨36,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨37,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨38,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨39,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨40,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨41,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨42,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨43,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨44,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨45,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨46,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨47,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨48,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨49,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨50,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨51,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12427) (by norm_num)
        (q := 1 - (cell12427 ⟨52,by decide⟩).lower)
        (by norm_num [cell12427]) (by norm_num [cell12427])
      exact ⟨E.1,E.2.trans (by norm_num [cell12427])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12427

/-! Source-cell containment and simple scalar guards at 12427. -/
namespace BstLean.Part269.N12427
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12427)
open BstLean.Part268 (cell12427)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12427 ⟨10,by decide⟩).lower ∧ (cell12427 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12427 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12427 ⟨11,by decide⟩).lower ∧ (cell12427 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12427 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12427 ⟨12,by decide⟩).lower ∧ (cell12427 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12427 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12427 ⟨13,by decide⟩).lower ∧ (cell12427 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12427 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12427 ⟨14,by decide⟩).lower ∧ (cell12427 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12427 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12427 ⟨15,by decide⟩).lower ∧ (cell12427 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12427 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12427 ⟨16,by decide⟩).lower ∧ (cell12427 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12427 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12427 ⟨17,by decide⟩).lower ∧ (cell12427 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12427 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12427 ⟨18,by decide⟩).lower ∧ (cell12427 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12427 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12427 ⟨19,by decide⟩).lower ∧ (cell12427 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12427 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12427 ⟨20,by decide⟩).lower ∧ (cell12427 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12427 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12427 ⟨21,by decide⟩).lower ∧ (cell12427 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12427 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12427 ⟨22,by decide⟩).lower ∧ (cell12427 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12427 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12427 ⟨23,by decide⟩).lower ∧ (cell12427 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12427 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12427 ⟨24,by decide⟩).lower ∧ (cell12427 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12427 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12427 ⟨25,by decide⟩).lower ∧ (cell12427 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12427 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12427 ⟨26,by decide⟩).lower ∧ (cell12427 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12427 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12427 ⟨27,by decide⟩).lower ∧ (cell12427 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12427 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12427 ⟨28,by decide⟩).lower ∧ (cell12427 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12427 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12427 ⟨29,by decide⟩).lower ∧ (cell12427 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12427 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12427 ⟨30,by decide⟩).lower ∧ (cell12427 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12427 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12427 ⟨31,by decide⟩).lower ∧ (cell12427 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12427 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12427 ⟨32,by decide⟩).lower ∧ (cell12427 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12427 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12427 ⟨33,by decide⟩).lower ∧ (cell12427 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12427 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12427 ⟨34,by decide⟩).lower ∧ (cell12427 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12427 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12427 ⟨35,by decide⟩).lower ∧ (cell12427 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12427 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12427 ⟨36,by decide⟩).lower ∧ (cell12427 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12427 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12427 ⟨37,by decide⟩).lower ∧ (cell12427 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12427 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12427 ⟨38,by decide⟩).lower ∧ (cell12427 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12427 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12427 ⟨39,by decide⟩).lower ∧ (cell12427 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12427 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12427 ⟨40,by decide⟩).lower ∧ (cell12427 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12427 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12427 ⟨41,by decide⟩).lower ∧ (cell12427 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12427 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12427 ⟨42,by decide⟩).lower ∧ (cell12427 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12427 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12427 ⟨43,by decide⟩).lower ∧ (cell12427 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12427 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12427 ⟨44,by decide⟩).lower ∧ (cell12427 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12427 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12427 ⟨45,by decide⟩).lower ∧ (cell12427 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12427 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12427 ⟨46,by decide⟩).lower ∧ (cell12427 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12427 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12427 ⟨47,by decide⟩).lower ∧ (cell12427 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12427 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12427 ⟨48,by decide⟩).lower ∧ (cell12427 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12427 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12427 ⟨49,by decide⟩).lower ∧ (cell12427 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12427 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12427 ⟨50,by decide⟩).lower ∧ (cell12427 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12427 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12427 ⟨51,by decide⟩).lower ∧ (cell12427 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12427 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12427 ⟨52,by decide⟩).lower ∧ (cell12427 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12427 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12427 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12427 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12427,cell12427,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12427 i).lower ∧
    (cell12427 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12427 i).upper ≤ (0.532 : ℝ) ∧
    (cell12427 i).centre ≤ (0.1 : ℝ) ∧ (cell12427 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12427 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12427 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12427

/-! The local source numeric instances at 12427 have no network premises. -/
namespace BstLean.Part269.N12427
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12427)
open BstLean.Part268 (cell12427)

noncomputable def sourceNumerics12427 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12427 (cell12427 i)
      scalarRow12427.M scalarRow12427.H scalarRow12427.xi := by
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
    energy_allowance := scalarRow12427.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12427]
    centre_nonneg := (scalarRow12427.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12427])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12427
/-! Actual 12428 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12428
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12428 ≤ (1.036202426803 : ℝ) := by
  have hr : (111.480940074974 : ℝ) ≤ √(12428 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.480940074974 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12428 12428 (11 / 1000) ≤
    (0.008574444285 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12428) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.480940074974 : ℝ) ≤ √(12428 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12428)
  have hdiv : K / √(12428 : ℝ) ≤ K / 111.480940074974 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.480940074974 ≤ (0.008574444285 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12428.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12428 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12428 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12428 := gPlus_lower 12428
end BstLean.Part269.N12428

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12428
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036202426802 : ℝ) ≤ wn 12428 := by
  have hn : √(12428 : ℝ) ≤ 111.480940074975 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12428 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.480940074975 ≤ 2 / √(12428 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257491259 : ℝ) ≤ rhoBar 12428 BstLean.Part154.csC ∧
    rhoBar 12428 BstLean.Part154.csC ≤ 0.000257491658 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036202426802 : ℝ) / (1.295212 * 12428) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036202426803 : ℝ) / (1.29521 * 12428) := by gcongr
      _ ≤ (0.000257491658 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12428 BstLean.Part154.csC) ≤ 0.001030032934 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12428 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12428 BstLean.Part154.csC) (piBar (rhoBar 12428 BstLean.Part154.csC)) ≤ 0.000196674069 ∧
    cc1 (rhoBar 12428 BstLean.Part154.csC) (piBar (rhoBar 12428 BstLean.Part154.csC)) ≤ 0.000125144974 ∧
    cc2 (rhoBar 12428 BstLean.Part154.csC) ≤ 0.000072647565 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12428 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12428 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12428 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12428 BstLean.Part154.csC * nuR (rhoBar 12428 BstLean.Part154.csC)) ≤ 0.000514999892 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257491658 : ℝ) * 0.001030032934 := by gcongr
      _ ≤ (0.000514999892 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12428 BstLean.Part154.csC) * nuR (rhoBar 12428 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001030032934 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12428 BstLean.Part154.csC) * rhoBar 12428 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257491658 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257491658 / 2 + 0.399 * 0.001030032934 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196674069 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514999892 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125144974 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257491658 / 1.414213562 := by gcongr
      _ ≤ (0.000072647565 : ℝ) := by norm_num

end BstLean.Part269.N12428

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12428
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12428 BstLean.Part154.csC) (piBar (rhoBar 12428 BstLean.Part154.csC)) ≤ 1.67043E-7 := by
  have hr0 : 0 ≤ rhoBar 12428 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12428 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12428 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12428 BstLean.Part154.csC) (piBar (rhoBar 12428 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12428 BstLean.Part154.csC) (piBar (rhoBar 12428 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12428 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196674069 : ℝ) ^ 2 + 0.000125144974 ^ 2 + 3 * 0.000072647565 ^ 2 +
        2 * 0.797885 * 0.000196674069 * 0.000125144974 + 2 * 0.000196674069 * 0.000072647565 +
        4 * 0.797885 * 0.000125144974 * 0.000072647565 := by gcongr
    _ ≤ (1.67043E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12428 BstLean.Part154.csC Θ ≤ 0.002688873598 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12428 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12428 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12428 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12428 BstLean.Part154.csC) (piBar (rhoBar 12428 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12428 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036202426803 * 1.67043E-7 / (0.000257491259 : ℝ) := by gcongr
    _ ≤ 0.002688873598 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12428 BstLean.Part154.csC Θ ≤ 0.002984587613 + 0.000679435092 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12428 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12428 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12428 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036202426803 : ℝ) * ((2 * Θ * 0.000257491658 +
        (6863 / 10000) * 0.000257491658 * 12428 * 0.001030032934) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002984587613 + 0.000679435092 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12428 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12428 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12428 0.011 Θ ∧ gammaRatio 12428 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12428 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036202426803 : ℝ) * 0.525 / ((1 - 0.011) * 12428) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12428 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12428 0.011 Θ) :=
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
    badAllowance 12428 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12428 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12428 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12428 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12428 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12428 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12428 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12428 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12428 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12428 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12428 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036202426803 : ℝ) * 12428 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12428 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004184587613 + 0.003368308690 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12428

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12428
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12428 BstLean.Part154.csC) (piBar (rhoBar 12428 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12428 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12428 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12428 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12428 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12428 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12428 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12428 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12428 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12428 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12428 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12428 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12428 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12428 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12428 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053061803247 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12428) ≤ 0.010712482154 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12428 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036202426803)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010712482154 + 2 * 0.737676 / 12428) := by gcongr
    _ ≤ (0.053061803247 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12428 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12428

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12428
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490998430 : ℝ) ≤ plow 12428 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12428) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053459549676)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411658639) : eMP 12428 0.011 xi bn ≤ 0.001215018091 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12428 : ℝ) * (1 - 0.011))) ≤ 0.000600677048 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001411658639 / (12428 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000600677048 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000600677048 : ℝ) + 3.141593 * 0.053459549676 / (12428 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001215018091 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053459549676)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411658639) : PiBarMP 12428 12 0.011 xi bn ≤ 0.163027025731 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12428 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037572045979 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.866099417270 : ℝ) ≤ √((12428 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.480940074974 : ℝ) ≤ √(12428 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12428) ≤ 0.124975697670 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037572045979 + 0.053459549676 * 1.772454 / (2 * (110.866099417270 : ℝ))) * (1 + 0.001215018091) +
        8 / (12428 * 111.480940074974) + 0.124975697670 := by gcongr
    _ ≤ (0.163027025731 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053459549676)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411658639) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284275015837) :
    parallelOracle 12428 0.011 xi bn cd ≤ 0.164044539542 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12428 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12428 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490998430 : ℝ) ≤ plow 12428 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.480940074974 : ℝ) ≤ √(12428 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284275015837 : ℝ) / (2 * 0.560490998430 * 111.480940074974)) * 0.163027025731 +
        0.284275015837 ^ 2 / (2 * 0.560490998430 * 111.480940074974) := by gcongr
    _ ≤ (0.164044539542 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053459549676) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411658639)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284275015837) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12428 12428 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490998430 : ℝ) ≤ plow 12428 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.480940074974 : ℝ) ≤ √(12428 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12428 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12428 Θ 1.22 ≤ 0.011895311424 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.480940074974 := by gcongr <;> linarith
      _ ≤ (0.011895311424 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12428 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12428 12428 0.011 ≤ 0.008574444285 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12428 12428 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12428 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12428 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12428 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12428 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164044539542 + 0.011895311424 + (0.008574444285 : ℝ) *
        (1 + 2 * (0.284275015837 + 0.011895311424) / (0.560490998430 * 111.480940074974))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12428]

end BstLean.Part269.N12428

/-! The original eight local profiles supply actual 12428 moment certificates. -/
namespace BstLean.Part269.N12428
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12428 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12428 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12428 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053459549676 ∧
    0 ≤ bN 12428 BstLean.Part154.csC (groupTheta g) ∧ bN 12428 BstLean.Part154.csC (groupTheta g) ≤ 0.001411658639 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12428 12428 0.011
      (momentAllowance 12428 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12428 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12428 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12428 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12428 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12428 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231213212590 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12428 0.011
      (momentAllowance 12428 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12428 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12428
/-! The actual computed-centre upper energy formula at 12428. -/
namespace BstLean.Part269.N12428
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12428

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12428
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12428)
open BstLean.Part268 (cell12428)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086327615997
  | 2 => 0.087286797222
  | 3 => 0.088246679929
  | 4 => 0.089209259407
  | 5 => 0.090176927759
  | 6 => 0.091152529994
  | 7 => 0.092139424895
  | 8 => 0.093141550602
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12428 12428 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12428 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12428

/-! Actual upper energy certificates on all 43 source endpoints at 12428. -/
namespace BstLean.Part269.N12428
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12428)
open BstLean.Part268 (cell12428)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12428 (gMinus 12428) (1 - (cell12428 i).lower) ≤ 1 ∧
    energyUpper 12428 (gMinus 12428) (BstLean.Part211.gPlus 12428)
      (finiteEnergy 12428 12428 0.011) (1 - (cell12428 i).lower) ≤
      (cell12428 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨10,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨11,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨12,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨13,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨14,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨15,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨16,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨17,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨18,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨19,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨20,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨21,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨22,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨23,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨24,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨25,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨26,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨27,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨28,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨29,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨30,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨31,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨32,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨33,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨34,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨35,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨36,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨37,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨38,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨39,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨40,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨41,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨42,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨43,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨44,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨45,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨46,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨47,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨48,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨49,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨50,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨51,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12428) (by norm_num)
        (q := 1 - (cell12428 ⟨52,by decide⟩).lower)
        (by norm_num [cell12428]) (by norm_num [cell12428])
      exact ⟨E.1,E.2.trans (by norm_num [cell12428])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12428

/-! Source-cell containment and simple scalar guards at 12428. -/
namespace BstLean.Part269.N12428
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12428)
open BstLean.Part268 (cell12428)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12428 ⟨10,by decide⟩).lower ∧ (cell12428 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12428 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12428 ⟨11,by decide⟩).lower ∧ (cell12428 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12428 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12428 ⟨12,by decide⟩).lower ∧ (cell12428 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12428 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12428 ⟨13,by decide⟩).lower ∧ (cell12428 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12428 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12428 ⟨14,by decide⟩).lower ∧ (cell12428 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12428 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12428 ⟨15,by decide⟩).lower ∧ (cell12428 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12428 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12428 ⟨16,by decide⟩).lower ∧ (cell12428 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12428 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12428 ⟨17,by decide⟩).lower ∧ (cell12428 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12428 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12428 ⟨18,by decide⟩).lower ∧ (cell12428 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12428 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12428 ⟨19,by decide⟩).lower ∧ (cell12428 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12428 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12428 ⟨20,by decide⟩).lower ∧ (cell12428 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12428 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12428 ⟨21,by decide⟩).lower ∧ (cell12428 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12428 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12428 ⟨22,by decide⟩).lower ∧ (cell12428 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12428 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12428 ⟨23,by decide⟩).lower ∧ (cell12428 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12428 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12428 ⟨24,by decide⟩).lower ∧ (cell12428 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12428 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12428 ⟨25,by decide⟩).lower ∧ (cell12428 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12428 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12428 ⟨26,by decide⟩).lower ∧ (cell12428 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12428 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12428 ⟨27,by decide⟩).lower ∧ (cell12428 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12428 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12428 ⟨28,by decide⟩).lower ∧ (cell12428 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12428 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12428 ⟨29,by decide⟩).lower ∧ (cell12428 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12428 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12428 ⟨30,by decide⟩).lower ∧ (cell12428 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12428 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12428 ⟨31,by decide⟩).lower ∧ (cell12428 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12428 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12428 ⟨32,by decide⟩).lower ∧ (cell12428 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12428 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12428 ⟨33,by decide⟩).lower ∧ (cell12428 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12428 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12428 ⟨34,by decide⟩).lower ∧ (cell12428 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12428 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12428 ⟨35,by decide⟩).lower ∧ (cell12428 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12428 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12428 ⟨36,by decide⟩).lower ∧ (cell12428 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12428 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12428 ⟨37,by decide⟩).lower ∧ (cell12428 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12428 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12428 ⟨38,by decide⟩).lower ∧ (cell12428 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12428 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12428 ⟨39,by decide⟩).lower ∧ (cell12428 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12428 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12428 ⟨40,by decide⟩).lower ∧ (cell12428 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12428 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12428 ⟨41,by decide⟩).lower ∧ (cell12428 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12428 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12428 ⟨42,by decide⟩).lower ∧ (cell12428 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12428 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12428 ⟨43,by decide⟩).lower ∧ (cell12428 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12428 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12428 ⟨44,by decide⟩).lower ∧ (cell12428 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12428 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12428 ⟨45,by decide⟩).lower ∧ (cell12428 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12428 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12428 ⟨46,by decide⟩).lower ∧ (cell12428 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12428 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12428 ⟨47,by decide⟩).lower ∧ (cell12428 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12428 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12428 ⟨48,by decide⟩).lower ∧ (cell12428 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12428 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12428 ⟨49,by decide⟩).lower ∧ (cell12428 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12428 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12428 ⟨50,by decide⟩).lower ∧ (cell12428 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12428 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12428 ⟨51,by decide⟩).lower ∧ (cell12428 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12428 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12428 ⟨52,by decide⟩).lower ∧ (cell12428 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12428 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12428 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12428 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12428,cell12428,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12428 i).lower ∧
    (cell12428 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12428 i).upper ≤ (0.532 : ℝ) ∧
    (cell12428 i).centre ≤ (0.1 : ℝ) ∧ (cell12428 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12428 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12428 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12428

/-! The local source numeric instances at 12428 have no network premises. -/
namespace BstLean.Part269.N12428
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12428)
open BstLean.Part268 (cell12428)

noncomputable def sourceNumerics12428 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12428 (cell12428 i)
      scalarRow12428.M scalarRow12428.H scalarRow12428.xi := by
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
    energy_allowance := scalarRow12428.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12428]
    centre_nonneg := (scalarRow12428.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12428])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12428
/-! Actual 12429 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12429
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12429 ≤ (1.036200957457 : ℝ) := by
  have hr : (111.485425056372 : ℝ) ≤ √(12429 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.485425056372 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12429 12429 (11 / 1000) ≤
    (0.008574099339 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12429) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.485425056372 : ℝ) ≤ √(12429 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12429)
  have hdiv : K / √(12429 : ℝ) ≤ K / 111.485425056372 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.485425056372 ≤ (0.008574099339 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12429.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12429 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12429 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12429 := gPlus_lower 12429
end BstLean.Part269.N12429

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12429
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036200957456 : ℝ) ≤ wn 12429 := by
  have hn : √(12429 : ℝ) ≤ 111.485425056373 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12429 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.485425056373 ≤ 2 / √(12429 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257470177 : ℝ) ≤ rhoBar 12429 BstLean.Part154.csC ∧
    rhoBar 12429 BstLean.Part154.csC ≤ 0.000257470576 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036200957456 : ℝ) / (1.295212 * 12429) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036200957457 : ℝ) / (1.29521 * 12429) := by gcongr
      _ ≤ (0.000257470576 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12429 BstLean.Part154.csC) ≤ 0.001029948596 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12429 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12429 BstLean.Part154.csC) (piBar (rhoBar 12429 BstLean.Part154.csC)) ≤ 0.000196657966 ∧
    cc1 (rhoBar 12429 BstLean.Part154.csC) (piBar (rhoBar 12429 BstLean.Part154.csC)) ≤ 0.000125134728 ∧
    cc2 (rhoBar 12429 BstLean.Part154.csC) ≤ 0.000072641617 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12429 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12429 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12429 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12429 BstLean.Part154.csC * nuR (rhoBar 12429 BstLean.Part154.csC)) ≤ 0.000514957725 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257470576 : ℝ) * 0.001029948596 := by gcongr
      _ ≤ (0.000514957725 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12429 BstLean.Part154.csC) * nuR (rhoBar 12429 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001029948596 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12429 BstLean.Part154.csC) * rhoBar 12429 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257470576 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257470576 / 2 + 0.399 * 0.001029948596 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196657966 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514957725 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125134728 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257470576 / 1.414213562 := by gcongr
      _ ≤ (0.000072641617 : ℝ) := by norm_num

end BstLean.Part269.N12429

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12429
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12429 BstLean.Part154.csC) (piBar (rhoBar 12429 BstLean.Part154.csC)) ≤ 1.67016E-7 := by
  have hr0 : 0 ≤ rhoBar 12429 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12429 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12429 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12429 BstLean.Part154.csC) (piBar (rhoBar 12429 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12429 BstLean.Part154.csC) (piBar (rhoBar 12429 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12429 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196657966 : ℝ) ^ 2 + 0.000125134728 ^ 2 + 3 * 0.000072641617 ^ 2 +
        2 * 0.797885 * 0.000196657966 * 0.000125134728 + 2 * 0.000196657966 * 0.000072641617 +
        4 * 0.797885 * 0.000125134728 * 0.000072641617 := by gcongr
    _ ≤ (1.67016E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12429 BstLean.Part154.csC Θ ≤ 0.002688655302 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12429 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12429 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12429 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12429 BstLean.Part154.csC) (piBar (rhoBar 12429 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12429 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036200957457 * 1.67016E-7 / (0.000257470177 : ℝ) := by gcongr
    _ ≤ 0.002688655302 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12429 BstLean.Part154.csC Θ ≤ 0.002984334776 + 0.000679378500 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12429 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12429 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12429 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036200957457 : ℝ) * ((2 * Θ * 0.000257470576 +
        (6863 / 10000) * 0.000257470576 * 12429 * 0.001029948596) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002984334776 + 0.000679378500 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12429 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12429 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12429 0.011 Θ ∧ gammaRatio 12429 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12429 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036200957457 : ℝ) * 0.525 / ((1 - 0.011) * 12429) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12429 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12429 0.011 Θ) :=
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
    badAllowance 12429 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12429 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12429 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12429 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12429 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12429 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12429 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12429 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12429 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12429 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12429 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036200957457 : ℝ) * 12429 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12429 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004184334776 + 0.003368033802 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12429

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12429
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12429 BstLean.Part154.csC) (piBar (rhoBar 12429 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12429 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12429 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12429 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12429 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12429 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12429 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12429 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12429 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12429 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12429 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12429 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12429 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12429 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12429 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053059645216 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12429) ≤ 0.010712051199 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12429 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036200957457)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010712051199 + 2 * 0.737676 / 12429) := by gcongr
    _ ≤ (0.053059645216 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12429 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12429

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12429
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491045651 : ℝ) ≤ plow 12429 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12429) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053459152523)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411544034) : eMP 12429 0.011 xi bn ≤ 0.001214919796 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12429 : ℝ) * (1 - 0.011))) ≤ 0.000600628501 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001411544034 / (12429 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000600628501 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000600628501 : ℝ) + 3.141593 * 0.053459152523 / (12429 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001214919796 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053459152523)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411544034) : PiBarMP 12429 12 0.011 xi bn ≤ 0.163020446203 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12429 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037570520811 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.870559663059 : ℝ) ≤ √((12429 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.485425056372 : ℝ) ≤ √(12429 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12429) ≤ 0.124970669985 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037570520811 + 0.053459152523 * 1.772454 / (2 * (110.870559663059 : ℝ))) * (1 + 0.001214919796) +
        8 / (12429 * 111.485425056372) + 0.124970669985 := by gcongr
    _ ≤ (0.163020446203 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053459152523)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411544034) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284271998959) :
    parallelOracle 12429 0.011 xi bn cd ≤ 0.164037886368 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12429 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12429 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491045651 : ℝ) ≤ plow 12429 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.485425056372 : ℝ) ≤ √(12429 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284271998959 : ℝ) / (2 * 0.560491045651 * 111.485425056372)) * 0.163020446203 +
        0.284271998959 ^ 2 / (2 * 0.560491045651 * 111.485425056372) := by gcongr
    _ ≤ (0.164037886368 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053459152523) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411544034)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284271998959) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12429 12429 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491045651 : ℝ) ≤ plow 12429 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.485425056372 : ℝ) ≤ √(12429 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12429 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12429 Θ 1.22 ≤ 0.011894832884 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.485425056372 := by gcongr <;> linarith
      _ ≤ (0.011894832884 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12429 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12429 12429 0.011 ≤ 0.008574099339 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12429 12429 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12429 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12429 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12429 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12429 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164037886368 + 0.011894832884 + (0.008574099339 : ℝ) *
        (1 + 2 * (0.284271998959 + 0.011894832884) / (0.560491045651 * 111.485425056372))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12429]

end BstLean.Part269.N12429

/-! The original eight local profiles supply actual 12429 moment certificates. -/
namespace BstLean.Part269.N12429
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12429 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12429 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12429 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053459152523 ∧
    0 ≤ bN 12429 BstLean.Part154.csC (groupTheta g) ∧ bN 12429 BstLean.Part154.csC (groupTheta g) ≤ 0.001411544034 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12429 12429 0.011
      (momentAllowance 12429 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12429 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12429 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12429 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12429 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12429 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231212353743 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12429 0.011
      (momentAllowance 12429 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12429 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12429
/-! The actual computed-centre upper energy formula at 12429. -/
namespace BstLean.Part269.N12429
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12429

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12429
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12429)
open BstLean.Part268 (cell12429)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086324359760
  | 2 => 0.087283472913
  | 3 => 0.088243276338
  | 4 => 0.089205762848
  | 5 => 0.090173321647
  | 6 => 0.091148794383
  | 7 => 0.092135535955
  | 8 => 0.093137480051
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12429 12429 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12429 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12429

/-! Actual upper energy certificates on all 43 source endpoints at 12429. -/
namespace BstLean.Part269.N12429
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12429)
open BstLean.Part268 (cell12429)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12429 (gMinus 12429) (1 - (cell12429 i).lower) ≤ 1 ∧
    energyUpper 12429 (gMinus 12429) (BstLean.Part211.gPlus 12429)
      (finiteEnergy 12429 12429 0.011) (1 - (cell12429 i).lower) ≤
      (cell12429 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨10,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨11,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨12,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨13,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨14,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨15,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨16,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨17,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨18,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨19,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨20,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨21,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨22,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨23,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨24,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨25,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨26,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨27,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨28,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨29,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨30,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨31,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨32,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨33,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨34,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨35,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨36,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨37,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨38,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨39,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨40,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨41,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨42,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨43,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨44,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨45,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨46,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨47,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨48,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨49,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨50,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨51,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12429) (by norm_num)
        (q := 1 - (cell12429 ⟨52,by decide⟩).lower)
        (by norm_num [cell12429]) (by norm_num [cell12429])
      exact ⟨E.1,E.2.trans (by norm_num [cell12429])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12429

/-! Source-cell containment and simple scalar guards at 12429. -/
namespace BstLean.Part269.N12429
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12429)
open BstLean.Part268 (cell12429)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12429 ⟨10,by decide⟩).lower ∧ (cell12429 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12429 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12429 ⟨11,by decide⟩).lower ∧ (cell12429 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12429 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12429 ⟨12,by decide⟩).lower ∧ (cell12429 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12429 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12429 ⟨13,by decide⟩).lower ∧ (cell12429 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12429 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12429 ⟨14,by decide⟩).lower ∧ (cell12429 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12429 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12429 ⟨15,by decide⟩).lower ∧ (cell12429 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12429 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12429 ⟨16,by decide⟩).lower ∧ (cell12429 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12429 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12429 ⟨17,by decide⟩).lower ∧ (cell12429 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12429 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12429 ⟨18,by decide⟩).lower ∧ (cell12429 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12429 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12429 ⟨19,by decide⟩).lower ∧ (cell12429 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12429 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12429 ⟨20,by decide⟩).lower ∧ (cell12429 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12429 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12429 ⟨21,by decide⟩).lower ∧ (cell12429 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12429 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12429 ⟨22,by decide⟩).lower ∧ (cell12429 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12429 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12429 ⟨23,by decide⟩).lower ∧ (cell12429 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12429 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12429 ⟨24,by decide⟩).lower ∧ (cell12429 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12429 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12429 ⟨25,by decide⟩).lower ∧ (cell12429 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12429 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12429 ⟨26,by decide⟩).lower ∧ (cell12429 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12429 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12429 ⟨27,by decide⟩).lower ∧ (cell12429 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12429 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12429 ⟨28,by decide⟩).lower ∧ (cell12429 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12429 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12429 ⟨29,by decide⟩).lower ∧ (cell12429 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12429 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12429 ⟨30,by decide⟩).lower ∧ (cell12429 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12429 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12429 ⟨31,by decide⟩).lower ∧ (cell12429 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12429 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12429 ⟨32,by decide⟩).lower ∧ (cell12429 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12429 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12429 ⟨33,by decide⟩).lower ∧ (cell12429 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12429 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12429 ⟨34,by decide⟩).lower ∧ (cell12429 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12429 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12429 ⟨35,by decide⟩).lower ∧ (cell12429 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12429 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12429 ⟨36,by decide⟩).lower ∧ (cell12429 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12429 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12429 ⟨37,by decide⟩).lower ∧ (cell12429 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12429 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12429 ⟨38,by decide⟩).lower ∧ (cell12429 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12429 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12429 ⟨39,by decide⟩).lower ∧ (cell12429 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12429 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12429 ⟨40,by decide⟩).lower ∧ (cell12429 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12429 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12429 ⟨41,by decide⟩).lower ∧ (cell12429 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12429 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12429 ⟨42,by decide⟩).lower ∧ (cell12429 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12429 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12429 ⟨43,by decide⟩).lower ∧ (cell12429 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12429 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12429 ⟨44,by decide⟩).lower ∧ (cell12429 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12429 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12429 ⟨45,by decide⟩).lower ∧ (cell12429 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12429 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12429 ⟨46,by decide⟩).lower ∧ (cell12429 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12429 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12429 ⟨47,by decide⟩).lower ∧ (cell12429 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12429 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12429 ⟨48,by decide⟩).lower ∧ (cell12429 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12429 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12429 ⟨49,by decide⟩).lower ∧ (cell12429 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12429 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12429 ⟨50,by decide⟩).lower ∧ (cell12429 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12429 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12429 ⟨51,by decide⟩).lower ∧ (cell12429 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12429 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12429 ⟨52,by decide⟩).lower ∧ (cell12429 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12429 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12429 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12429 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12429,cell12429,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12429 i).lower ∧
    (cell12429 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12429 i).upper ≤ (0.532 : ℝ) ∧
    (cell12429 i).centre ≤ (0.1 : ℝ) ∧ (cell12429 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12429 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12429 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12429

/-! The local source numeric instances at 12429 have no network premises. -/
namespace BstLean.Part269.N12429
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12429)
open BstLean.Part268 (cell12429)

noncomputable def sourceNumerics12429 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12429 (cell12429 i)
      scalarRow12429.M scalarRow12429.H scalarRow12429.xi := by
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
    energy_allowance := scalarRow12429.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12429]
    centre_nonneg := (scalarRow12429.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12429])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12429
/-! Actual 12430 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12430
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12430 ≤ (1.036199488289 : ℝ) := by
  have hr : (111.489909857349 : ℝ) ≤ √(12430 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.489909857349 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12430 12430 (11 / 1000) ≤
    (0.008573754434 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12430) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.489909857349 : ℝ) ≤ √(12430 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12430)
  have hdiv : K / √(12430 : ℝ) ≤ K / 111.489909857349 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.489909857349 ≤ (0.008573754434 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12430.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12430 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12430 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12430 := gPlus_lower 12430
end BstLean.Part269.N12430

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12430
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036199488288 : ℝ) ≤ wn 12430 := by
  have hn : √(12430 : ℝ) ≤ 111.489909857350 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12430 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.489909857350 ≤ 2 / √(12430 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257449099 : ℝ) ≤ rhoBar 12430 BstLean.Part154.csC ∧
    rhoBar 12430 BstLean.Part154.csC ≤ 0.000257449497 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036199488288 : ℝ) / (1.295212 * 12430) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036199488289 : ℝ) / (1.29521 * 12430) := by gcongr
      _ ≤ (0.000257449497 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12430 BstLean.Part154.csC) ≤ 0.001029864269 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12430 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12430 BstLean.Part154.csC) (piBar (rhoBar 12430 BstLean.Part154.csC)) ≤ 0.000196641865 ∧
    cc1 (rhoBar 12430 BstLean.Part154.csC) (piBar (rhoBar 12430 BstLean.Part154.csC)) ≤ 0.000125124483 ∧
    cc2 (rhoBar 12430 BstLean.Part154.csC) ≤ 0.000072635670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12430 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12430 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12430 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12430 BstLean.Part154.csC * nuR (rhoBar 12430 BstLean.Part154.csC)) ≤ 0.000514915564 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257449497 : ℝ) * 0.001029864269 := by gcongr
      _ ≤ (0.000514915564 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12430 BstLean.Part154.csC) * nuR (rhoBar 12430 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001029864269 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12430 BstLean.Part154.csC) * rhoBar 12430 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257449497 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257449497 / 2 + 0.399 * 0.001029864269 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196641865 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514915564 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125124483 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257449497 / 1.414213562 := by gcongr
      _ ≤ (0.000072635670 : ℝ) := by norm_num

end BstLean.Part269.N12430

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12430
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12430 BstLean.Part154.csC) (piBar (rhoBar 12430 BstLean.Part154.csC)) ≤ 1.66989E-7 := by
  have hr0 : 0 ≤ rhoBar 12430 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12430 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12430 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12430 BstLean.Part154.csC) (piBar (rhoBar 12430 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12430 BstLean.Part154.csC) (piBar (rhoBar 12430 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12430 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196641865 : ℝ) ^ 2 + 0.000125124483 ^ 2 + 3 * 0.000072635670 ^ 2 +
        2 * 0.797885 * 0.000196641865 * 0.000125124483 + 2 * 0.000196641865 * 0.000072635670 +
        4 * 0.797885 * 0.000125124483 * 0.000072635670 := by gcongr
    _ ≤ (1.66989E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12430 BstLean.Part154.csC Θ ≤ 0.002688436931 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12430 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12430 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12430 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12430 BstLean.Part154.csC) (piBar (rhoBar 12430 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12430 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036199488289 * 1.66989E-7 / (0.000257449099 : ℝ) := by gcongr
    _ ≤ 0.002688436931 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12430 BstLean.Part154.csC Θ ≤ 0.002984081968 + 0.000679321916 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12430 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12430 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12430 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036199488289 : ℝ) * ((2 * Θ * 0.000257449497 +
        (6863 / 10000) * 0.000257449497 * 12430 * 0.001029864269) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002984081968 + 0.000679321916 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12430 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12430 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12430 0.011 Θ ∧ gammaRatio 12430 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12430 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036199488289 : ℝ) * 0.525 / ((1 - 0.011) * 12430) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12430 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12430 0.011 Θ) :=
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
    badAllowance 12430 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12430 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12430 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12430 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12430 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12430 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12430 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12430 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12430 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12430 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12430 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036199488289 : ℝ) * 12430 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12430 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004184081968 + 0.003367758847 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12430

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12430
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12430 BstLean.Part154.csC) (piBar (rhoBar 12430 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12430 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12430 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12430 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12430 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12430 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12430 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12430 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12430 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12430 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12430 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12430 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12430 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12430 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12430 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053057487442 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12430) ≤ 0.010711620295 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12430 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036199488289)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010711620295 + 2 * 0.737676 / 12430) := by gcongr
    _ ≤ (0.053057487442 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12430 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12430

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12430
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491092864 : ℝ) ≤ plow 12430 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12430) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053458755363)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411429389) : eMP 12430 0.011 xi bn ≤ 0.001214821492 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12430 : ℝ) * (1 - 0.011))) ≤ 0.000600579949 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001411429389 / (12430 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000600579949 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000600579949 : ℝ) + 3.141593 * 0.053458755363 / (12430 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001214821492 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053458755363)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411429389) : PiBarMP 12430 12 0.011 xi bn ≤ 0.163013866689 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12430 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037568995050 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.875019729423 : ℝ) ≤ √((12430 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.489909857349 : ℝ) ≤ √(12430 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12430) ≤ 0.124965642906 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037568995050 + 0.053458755363 * 1.772454 / (2 * (110.875019729423 : ℝ))) * (1 + 0.001214821492) +
        8 / (12430 * 111.489909857349) + 0.124965642906 := by gcongr
    _ ≤ (0.163013866689 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053458755363)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411429389) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284268982319) :
    parallelOracle 12430 0.011 xi bn cd ≤ 0.164031233217 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12430 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12430 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491092864 : ℝ) ≤ plow 12430 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.489909857349 : ℝ) ≤ √(12430 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284268982319 : ℝ) / (2 * 0.560491092864 * 111.489909857349)) * 0.163013866689 +
        0.284268982319 ^ 2 / (2 * 0.560491092864 * 111.489909857349) := by gcongr
    _ ≤ (0.164031233217 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053458755363) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411429389)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284268982319) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12430 12430 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491092864 : ℝ) ≤ plow 12430 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.489909857349 : ℝ) ≤ √(12430 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12430 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12430 Θ 1.22 ≤ 0.011894354402 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.489909857349 := by gcongr <;> linarith
      _ ≤ (0.011894354402 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12430 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12430 12430 0.011 ≤ 0.008573754434 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12430 12430 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12430 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12430 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12430 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12430 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164031233217 + 0.011894354402 + (0.008573754434 : ℝ) *
        (1 + 2 * (0.284268982319 + 0.011894354402) / (0.560491092864 * 111.489909857349))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12430]

end BstLean.Part269.N12430

/-! The original eight local profiles supply actual 12430 moment certificates. -/
namespace BstLean.Part269.N12430
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12430 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12430 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12430 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053458755363 ∧
    0 ≤ bN 12430 BstLean.Part154.csC (groupTheta g) ∧ bN 12430 BstLean.Part154.csC (groupTheta g) ≤ 0.001411429389 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12430 12430 0.011
      (momentAllowance 12430 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12430 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12430 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12430 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12430 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12430 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231211494877 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12430 0.011
      (momentAllowance 12430 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12430 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12430
/-! The actual computed-centre upper energy formula at 12430. -/
namespace BstLean.Part269.N12430
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12430

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12430
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12430)
open BstLean.Part268 (cell12430)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086321104963
  | 2 => 0.087280150108
  | 3 => 0.088239874330
  | 4 => 0.089202267966
  | 5 => 0.090169717330
  | 6 => 0.091145060708
  | 7 => 0.092131649122
  | 8 => 0.093133411811
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12430 12430 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12430 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12430

/-! Actual upper energy certificates on all 43 source endpoints at 12430. -/
namespace BstLean.Part269.N12430
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12430)
open BstLean.Part268 (cell12430)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12430 (gMinus 12430) (1 - (cell12430 i).lower) ≤ 1 ∧
    energyUpper 12430 (gMinus 12430) (BstLean.Part211.gPlus 12430)
      (finiteEnergy 12430 12430 0.011) (1 - (cell12430 i).lower) ≤
      (cell12430 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨10,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨11,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨12,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨13,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨14,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨15,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨16,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨17,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨18,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨19,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨20,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨21,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨22,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨23,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨24,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨25,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨26,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨27,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨28,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨29,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨30,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨31,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨32,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨33,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨34,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨35,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨36,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨37,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨38,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨39,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨40,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨41,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨42,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨43,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨44,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨45,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨46,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨47,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨48,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨49,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨50,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨51,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12430) (by norm_num)
        (q := 1 - (cell12430 ⟨52,by decide⟩).lower)
        (by norm_num [cell12430]) (by norm_num [cell12430])
      exact ⟨E.1,E.2.trans (by norm_num [cell12430])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12430

/-! Source-cell containment and simple scalar guards at 12430. -/
namespace BstLean.Part269.N12430
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12430)
open BstLean.Part268 (cell12430)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12430 ⟨10,by decide⟩).lower ∧ (cell12430 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12430 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12430 ⟨11,by decide⟩).lower ∧ (cell12430 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12430 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12430 ⟨12,by decide⟩).lower ∧ (cell12430 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12430 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12430 ⟨13,by decide⟩).lower ∧ (cell12430 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12430 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12430 ⟨14,by decide⟩).lower ∧ (cell12430 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12430 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12430 ⟨15,by decide⟩).lower ∧ (cell12430 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12430 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12430 ⟨16,by decide⟩).lower ∧ (cell12430 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12430 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12430 ⟨17,by decide⟩).lower ∧ (cell12430 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12430 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12430 ⟨18,by decide⟩).lower ∧ (cell12430 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12430 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12430 ⟨19,by decide⟩).lower ∧ (cell12430 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12430 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12430 ⟨20,by decide⟩).lower ∧ (cell12430 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12430 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12430 ⟨21,by decide⟩).lower ∧ (cell12430 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12430 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12430 ⟨22,by decide⟩).lower ∧ (cell12430 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12430 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12430 ⟨23,by decide⟩).lower ∧ (cell12430 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12430 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12430 ⟨24,by decide⟩).lower ∧ (cell12430 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12430 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12430 ⟨25,by decide⟩).lower ∧ (cell12430 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12430 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12430 ⟨26,by decide⟩).lower ∧ (cell12430 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12430 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12430 ⟨27,by decide⟩).lower ∧ (cell12430 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12430 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12430 ⟨28,by decide⟩).lower ∧ (cell12430 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12430 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12430 ⟨29,by decide⟩).lower ∧ (cell12430 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12430 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12430 ⟨30,by decide⟩).lower ∧ (cell12430 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12430 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12430 ⟨31,by decide⟩).lower ∧ (cell12430 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12430 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12430 ⟨32,by decide⟩).lower ∧ (cell12430 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12430 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12430 ⟨33,by decide⟩).lower ∧ (cell12430 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12430 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12430 ⟨34,by decide⟩).lower ∧ (cell12430 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12430 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12430 ⟨35,by decide⟩).lower ∧ (cell12430 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12430 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12430 ⟨36,by decide⟩).lower ∧ (cell12430 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12430 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12430 ⟨37,by decide⟩).lower ∧ (cell12430 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12430 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12430 ⟨38,by decide⟩).lower ∧ (cell12430 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12430 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12430 ⟨39,by decide⟩).lower ∧ (cell12430 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12430 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12430 ⟨40,by decide⟩).lower ∧ (cell12430 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12430 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12430 ⟨41,by decide⟩).lower ∧ (cell12430 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12430 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12430 ⟨42,by decide⟩).lower ∧ (cell12430 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12430 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12430 ⟨43,by decide⟩).lower ∧ (cell12430 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12430 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12430 ⟨44,by decide⟩).lower ∧ (cell12430 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12430 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12430 ⟨45,by decide⟩).lower ∧ (cell12430 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12430 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12430 ⟨46,by decide⟩).lower ∧ (cell12430 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12430 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12430 ⟨47,by decide⟩).lower ∧ (cell12430 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12430 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12430 ⟨48,by decide⟩).lower ∧ (cell12430 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12430 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12430 ⟨49,by decide⟩).lower ∧ (cell12430 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12430 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12430 ⟨50,by decide⟩).lower ∧ (cell12430 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12430 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12430 ⟨51,by decide⟩).lower ∧ (cell12430 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12430 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12430 ⟨52,by decide⟩).lower ∧ (cell12430 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12430 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12430 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12430 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12430,cell12430,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12430 i).lower ∧
    (cell12430 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12430 i).upper ≤ (0.532 : ℝ) ∧
    (cell12430 i).centre ≤ (0.1 : ℝ) ∧ (cell12430 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12430 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12430 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12430

/-! The local source numeric instances at 12430 have no network premises. -/
namespace BstLean.Part269.N12430
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12430)
open BstLean.Part268 (cell12430)

noncomputable def sourceNumerics12430 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12430 (cell12430 i)
      scalarRow12430.M scalarRow12430.H scalarRow12430.xi := by
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
    energy_allowance := scalarRow12430.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12430]
    centre_nonneg := (scalarRow12430.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12430])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12430
/-! Actual 12431 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12431
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12431 ≤ (1.036198019300 : ℝ) := by
  have hr : (111.494394477928 : ℝ) ≤ √(12431 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.494394477928 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12431 12431 (11 / 1000) ≤
    (0.008573409570 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12431) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.494394477928 : ℝ) ≤ √(12431 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12431)
  have hdiv : K / √(12431 : ℝ) ≤ K / 111.494394477928 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.494394477928 ≤ (0.008573409570 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12431.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12431 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12431 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12431 := gPlus_lower 12431
end BstLean.Part269.N12431

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12431
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036198019299 : ℝ) ≤ wn 12431 := by
  have hn : √(12431 : ℝ) ≤ 111.494394477929 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12431 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.494394477929 ≤ 2 / √(12431 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257428024 : ℝ) ≤ rhoBar 12431 BstLean.Part154.csC ∧
    rhoBar 12431 BstLean.Part154.csC ≤ 0.000257428422 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036198019299 : ℝ) / (1.295212 * 12431) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036198019300 : ℝ) / (1.29521 * 12431) := by gcongr
      _ ≤ (0.000257428422 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12431 BstLean.Part154.csC) ≤ 0.001029779958 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12431 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12431 BstLean.Part154.csC) (piBar (rhoBar 12431 BstLean.Part154.csC)) ≤ 0.000196625767 ∧
    cc1 (rhoBar 12431 BstLean.Part154.csC) (piBar (rhoBar 12431 BstLean.Part154.csC)) ≤ 0.000125114240 ∧
    cc2 (rhoBar 12431 BstLean.Part154.csC) ≤ 0.000072629724 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12431 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12431 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12431 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12431 BstLean.Part154.csC * nuR (rhoBar 12431 BstLean.Part154.csC)) ≤ 0.000514873412 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257428422 : ℝ) * 0.001029779958 := by gcongr
      _ ≤ (0.000514873412 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12431 BstLean.Part154.csC) * nuR (rhoBar 12431 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001029779958 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12431 BstLean.Part154.csC) * rhoBar 12431 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257428422 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257428422 / 2 + 0.399 * 0.001029779958 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196625767 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514873412 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125114240 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257428422 / 1.414213562 := by gcongr
      _ ≤ (0.000072629724 : ℝ) := by norm_num

end BstLean.Part269.N12431

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12431
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12431 BstLean.Part154.csC) (piBar (rhoBar 12431 BstLean.Part154.csC)) ≤ 1.66961E-7 := by
  have hr0 : 0 ≤ rhoBar 12431 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12431 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12431 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12431 BstLean.Part154.csC) (piBar (rhoBar 12431 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12431 BstLean.Part154.csC) (piBar (rhoBar 12431 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12431 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196625767 : ℝ) ^ 2 + 0.000125114240 ^ 2 + 3 * 0.000072629724 ^ 2 +
        2 * 0.797885 * 0.000196625767 * 0.000125114240 + 2 * 0.000196625767 * 0.000072629724 +
        4 * 0.797885 * 0.000125114240 * 0.000072629724 := by gcongr
    _ ≤ (1.66961E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12431 BstLean.Part154.csC Θ ≤ 0.002688202393 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12431 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12431 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12431 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12431 BstLean.Part154.csC) (piBar (rhoBar 12431 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12431 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036198019300 * 1.66961E-7 / (0.000257428024 : ℝ) := by gcongr
    _ ≤ 0.002688202393 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12431 BstLean.Part154.csC Θ ≤ 0.002983829215 + 0.000679265344 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12431 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12431 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12431 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036198019300 : ℝ) * ((2 * Θ * 0.000257428422 +
        (6863 / 10000) * 0.000257428422 * 12431 * 0.001029779958) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002983829215 + 0.000679265344 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12431 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12431 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12431 0.011 Θ ∧ gammaRatio 12431 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12431 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036198019300 : ℝ) * 0.525 / ((1 - 0.011) * 12431) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12431 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12431 0.011 Θ) :=
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
    badAllowance 12431 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12431 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12431 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12431 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12431 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12431 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12431 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12431 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12431 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12431 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12431 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036198019300 : ℝ) * 12431 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12431 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004183829215 + 0.003367467737 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12431

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12431
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12431 BstLean.Part154.csC) (piBar (rhoBar 12431 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12431 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12431 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12431 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12431 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12431 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12431 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12431 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12431 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12431 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12431 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12431 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12431 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12431 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12431 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053055329931 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12431) ≤ 0.010711189443 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12431 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036198019300)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010711189443 + 2 * 0.737676 / 12431) := by gcongr
    _ ≤ (0.053055329931 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12431 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12431

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12431
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491140069 : ℝ) ≤ plow 12431 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12431) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053458349777)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411306257) : eMP 12431 0.011 xi bn ≤ 0.001214719581 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12431 : ℝ) * (1 - 0.011))) ≤ 0.000600529595 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001411306257 / (12431 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000600529595 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000600529595 : ℝ) + 3.141593 * 0.053458349777 / (12431 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001214719581 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053458349777)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411306257) : PiBarMP 12431 12 0.011 xi bn ≤ 0.163007174421 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12431 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037567356269 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.879479616383 : ℝ) ≤ √((12431 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.494394477928 : ℝ) ≤ √(12431 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12431) ≤ 0.124960616433 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037567356269 + 0.053458349777 * 1.772454 / (2 * (110.879479616383 : ℝ))) * (1 + 0.001214719581) +
        8 / (12431 * 111.494394477928) + 0.124960616433 := by gcongr
    _ ≤ (0.163007174421 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053458349777)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411306257) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284265947718) :
    parallelOracle 12431 0.011 xi bn cd ≤ 0.164024466959 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12431 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12431 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491140069 : ℝ) ≤ plow 12431 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.494394477928 : ℝ) ≤ √(12431 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284265947718 : ℝ) / (2 * 0.560491140069 * 111.494394477928)) * 0.163007174421 +
        0.284265947718 ^ 2 / (2 * 0.560491140069 * 111.494394477928) := by gcongr
    _ ≤ (0.164024466959 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053458349777) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411306257)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284265947718) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12431 12431 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491140069 : ℝ) ≤ plow 12431 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.494394477928 : ℝ) ≤ √(12431 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12431 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12431 Θ 1.22 ≤ 0.011893875977 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.494394477928 := by gcongr <;> linarith
      _ ≤ (0.011893875977 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12431 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12431 12431 0.011 ≤ 0.008573409570 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12431 12431 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12431 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12431 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12431 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12431 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164024466959 + 0.011893875977 + (0.008573409570 : ℝ) *
        (1 + 2 * (0.284265947718 + 0.011893875977) / (0.560491140069 * 111.494394477928))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12431]

end BstLean.Part269.N12431

/-! The original eight local profiles supply actual 12431 moment certificates. -/
namespace BstLean.Part269.N12431
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12431 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12431 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12431 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053458349777 ∧
    0 ≤ bN 12431 BstLean.Part154.csC (groupTheta g) ∧ bN 12431 BstLean.Part154.csC (groupTheta g) ≤ 0.001411306257 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12431 12431 0.011
      (momentAllowance 12431 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12431 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12431 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12431 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12431 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12431 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231210617787 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12431 0.011
      (momentAllowance 12431 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12431 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12431
/-! The actual computed-centre upper energy formula at 12431. -/
namespace BstLean.Part269.N12431
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12431

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12431
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12431)
open BstLean.Part268 (cell12431)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086317851605
  | 2 => 0.087276828805
  | 3 => 0.088236473901
  | 4 => 0.089198774760
  | 5 => 0.090166114806
  | 6 => 0.091141328967
  | 7 => 0.092127764393
  | 8 => 0.093129345879
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12431 12431 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12431 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12431

/-! Actual upper energy certificates on all 43 source endpoints at 12431. -/
namespace BstLean.Part269.N12431
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12431)
open BstLean.Part268 (cell12431)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12431 (gMinus 12431) (1 - (cell12431 i).lower) ≤ 1 ∧
    energyUpper 12431 (gMinus 12431) (BstLean.Part211.gPlus 12431)
      (finiteEnergy 12431 12431 0.011) (1 - (cell12431 i).lower) ≤
      (cell12431 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨10,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨11,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨12,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨13,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨14,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨15,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨16,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨17,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨18,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨19,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨20,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨21,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨22,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨23,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨24,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨25,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨26,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨27,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨28,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨29,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨30,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨31,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨32,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨33,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨34,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨35,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨36,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨37,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨38,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨39,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨40,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨41,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨42,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨43,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨44,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨45,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨46,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨47,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨48,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨49,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨50,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨51,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12431) (by norm_num)
        (q := 1 - (cell12431 ⟨52,by decide⟩).lower)
        (by norm_num [cell12431]) (by norm_num [cell12431])
      exact ⟨E.1,E.2.trans (by norm_num [cell12431])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12431

/-! Source-cell containment and simple scalar guards at 12431. -/
namespace BstLean.Part269.N12431
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12431)
open BstLean.Part268 (cell12431)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12431 ⟨10,by decide⟩).lower ∧ (cell12431 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12431 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12431 ⟨11,by decide⟩).lower ∧ (cell12431 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12431 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12431 ⟨12,by decide⟩).lower ∧ (cell12431 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12431 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12431 ⟨13,by decide⟩).lower ∧ (cell12431 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12431 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12431 ⟨14,by decide⟩).lower ∧ (cell12431 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12431 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12431 ⟨15,by decide⟩).lower ∧ (cell12431 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12431 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12431 ⟨16,by decide⟩).lower ∧ (cell12431 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12431 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12431 ⟨17,by decide⟩).lower ∧ (cell12431 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12431 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12431 ⟨18,by decide⟩).lower ∧ (cell12431 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12431 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12431 ⟨19,by decide⟩).lower ∧ (cell12431 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12431 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12431 ⟨20,by decide⟩).lower ∧ (cell12431 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12431 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12431 ⟨21,by decide⟩).lower ∧ (cell12431 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12431 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12431 ⟨22,by decide⟩).lower ∧ (cell12431 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12431 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12431 ⟨23,by decide⟩).lower ∧ (cell12431 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12431 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12431 ⟨24,by decide⟩).lower ∧ (cell12431 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12431 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12431 ⟨25,by decide⟩).lower ∧ (cell12431 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12431 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12431 ⟨26,by decide⟩).lower ∧ (cell12431 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12431 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12431 ⟨27,by decide⟩).lower ∧ (cell12431 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12431 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12431 ⟨28,by decide⟩).lower ∧ (cell12431 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12431 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12431 ⟨29,by decide⟩).lower ∧ (cell12431 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12431 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12431 ⟨30,by decide⟩).lower ∧ (cell12431 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12431 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12431 ⟨31,by decide⟩).lower ∧ (cell12431 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12431 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12431 ⟨32,by decide⟩).lower ∧ (cell12431 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12431 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12431 ⟨33,by decide⟩).lower ∧ (cell12431 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12431 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12431 ⟨34,by decide⟩).lower ∧ (cell12431 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12431 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12431 ⟨35,by decide⟩).lower ∧ (cell12431 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12431 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12431 ⟨36,by decide⟩).lower ∧ (cell12431 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12431 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12431 ⟨37,by decide⟩).lower ∧ (cell12431 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12431 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12431 ⟨38,by decide⟩).lower ∧ (cell12431 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12431 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12431 ⟨39,by decide⟩).lower ∧ (cell12431 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12431 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12431 ⟨40,by decide⟩).lower ∧ (cell12431 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12431 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12431 ⟨41,by decide⟩).lower ∧ (cell12431 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12431 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12431 ⟨42,by decide⟩).lower ∧ (cell12431 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12431 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12431 ⟨43,by decide⟩).lower ∧ (cell12431 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12431 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12431 ⟨44,by decide⟩).lower ∧ (cell12431 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12431 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12431 ⟨45,by decide⟩).lower ∧ (cell12431 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12431 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12431 ⟨46,by decide⟩).lower ∧ (cell12431 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12431 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12431 ⟨47,by decide⟩).lower ∧ (cell12431 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12431 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12431 ⟨48,by decide⟩).lower ∧ (cell12431 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12431 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12431 ⟨49,by decide⟩).lower ∧ (cell12431 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12431 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12431 ⟨50,by decide⟩).lower ∧ (cell12431 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12431 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12431 ⟨51,by decide⟩).lower ∧ (cell12431 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12431 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12431 ⟨52,by decide⟩).lower ∧ (cell12431 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12431 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12431 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12431 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12431,cell12431,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12431 i).lower ∧
    (cell12431 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12431 i).upper ≤ (0.532 : ℝ) ∧
    (cell12431 i).centre ≤ (0.1 : ℝ) ∧ (cell12431 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12431 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12431 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12431

/-! The local source numeric instances at 12431 have no network premises. -/
namespace BstLean.Part269.N12431
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12431)
open BstLean.Part268 (cell12431)

noncomputable def sourceNumerics12431 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12431 (cell12431 i)
      scalarRow12431.M scalarRow12431.H scalarRow12431.xi := by
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
    energy_allowance := scalarRow12431.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12431]
    centre_nonneg := (scalarRow12431.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12431])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12431
/-! Actual 12432 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12432
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12432 ≤ (1.036196550489 : ℝ) := by
  have hr : (111.498878918130 : ℝ) ≤ √(12432 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.498878918130 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12432 12432 (11 / 1000) ≤
    (0.008573064748 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12432) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.498878918130 : ℝ) ≤ √(12432 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12432)
  have hdiv : K / √(12432 : ℝ) ≤ K / 111.498878918130 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.498878918130 ≤ (0.008573064748 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12432.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12432 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12432 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12432 := gPlus_lower 12432
end BstLean.Part269.N12432

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12432
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036196550488 : ℝ) ≤ wn 12432 := by
  have hn : √(12432 : ℝ) ≤ 111.498878918131 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12432 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.498878918131 ≤ 2 / √(12432 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257406952 : ℝ) ≤ rhoBar 12432 BstLean.Part154.csC ∧
    rhoBar 12432 BstLean.Part154.csC ≤ 0.000257407350 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036196550488 : ℝ) / (1.295212 * 12432) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036196550489 : ℝ) / (1.29521 * 12432) := by gcongr
      _ ≤ (0.000257407350 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12432 BstLean.Part154.csC) ≤ 0.001029695659 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12432 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12432 BstLean.Part154.csC) (piBar (rhoBar 12432 BstLean.Part154.csC)) ≤ 0.000196609671 ∧
    cc1 (rhoBar 12432 BstLean.Part154.csC) (piBar (rhoBar 12432 BstLean.Part154.csC)) ≤ 0.000125103998 ∧
    cc2 (rhoBar 12432 BstLean.Part154.csC) ≤ 0.000072623779 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12432 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12432 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12432 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12432 BstLean.Part154.csC * nuR (rhoBar 12432 BstLean.Part154.csC)) ≤ 0.000514831265 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257407350 : ℝ) * 0.001029695659 := by gcongr
      _ ≤ (0.000514831265 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12432 BstLean.Part154.csC) * nuR (rhoBar 12432 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001029695659 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12432 BstLean.Part154.csC) * rhoBar 12432 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257407350 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257407350 / 2 + 0.399 * 0.001029695659 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196609671 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514831265 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125103998 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257407350 / 1.414213562 := by gcongr
      _ ≤ (0.000072623779 : ℝ) := by norm_num

end BstLean.Part269.N12432

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12432
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12432 BstLean.Part154.csC) (piBar (rhoBar 12432 BstLean.Part154.csC)) ≤ 1.66934E-7 := by
  have hr0 : 0 ≤ rhoBar 12432 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12432 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12432 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12432 BstLean.Part154.csC) (piBar (rhoBar 12432 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12432 BstLean.Part154.csC) (piBar (rhoBar 12432 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12432 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196609671 : ℝ) ^ 2 + 0.000125103998 ^ 2 + 3 * 0.000072623779 ^ 2 +
        2 * 0.797885 * 0.000196609671 * 0.000125103998 + 2 * 0.000196609671 * 0.000072623779 +
        4 * 0.797885 * 0.000125103998 * 0.000072623779 := by gcongr
    _ ≤ (1.66934E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12432 BstLean.Part154.csC Θ ≤ 0.002687983889 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12432 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12432 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12432 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12432 BstLean.Part154.csC) (piBar (rhoBar 12432 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12432 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036196550489 * 1.66934E-7 / (0.000257406952 : ℝ) := by gcongr
    _ ≤ 0.002687983889 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12432 BstLean.Part154.csC Θ ≤ 0.002983576495 + 0.000679208779 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12432 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12432 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12432 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036196550489 : ℝ) * ((2 * Θ * 0.000257407350 +
        (6863 / 10000) * 0.000257407350 * 12432 * 0.001029695659) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002983576495 + 0.000679208779 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12432 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12432 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12432 0.011 Θ ∧ gammaRatio 12432 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12432 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036196550489 : ℝ) * 0.525 / ((1 - 0.011) * 12432) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12432 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12432 0.011 Θ) :=
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
    badAllowance 12432 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12432 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12432 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12432 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12432 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12432 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12432 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12432 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12432 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12432 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12432 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036196550489 : ℝ) * 12432 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12432 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004183576495 + 0.003367192668 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12432

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12432
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12432 BstLean.Part154.csC) (piBar (rhoBar 12432 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12432 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12432 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12432 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12432 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12432 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12432 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12432 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12432 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12432 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12432 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12432 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12432 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12432 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12432 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053053172682 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12432) ≤ 0.010710758643 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12432 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036196550489)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010710758643 + 2 * 0.737676 / 12432) := by gcongr
    _ ≤ (0.053053172682 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12432 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12432

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12432
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491187266 : ℝ) ≤ plow 12432 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12432) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053457952646)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411191542) : eMP 12432 0.011 xi bn ≤ 0.001214621263 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12432 : ℝ) * (1 - 0.011))) ≤ 0.000600481036 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001411191542 / (12432 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000600481036 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000600481036 : ℝ) + 3.141593 * 0.053457952646 / (12432 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001214621263 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053457952646)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411191542) : PiBarMP 12432 12 0.011 xi bn ≤ 0.163000595063 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12432 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037565829447 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.883939323961 : ℝ) ≤ √((12432 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.498878918130 : ℝ) ≤ √(12432 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12432) ≤ 0.124955590567 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037565829447 + 0.053457952646 * 1.772454 / (2 * (110.883939323961 : ℝ))) * (1 + 0.001214621263) +
        8 / (12432 * 111.498878918130) + 0.124955590567 := by gcongr
    _ ≤ (0.163000595063 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053457952646)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411191542) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284262931659) :
    parallelOracle 12432 0.011 xi bn cd ≤ 0.164017813984 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12432 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12432 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491187266 : ℝ) ≤ plow 12432 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.498878918130 : ℝ) ≤ √(12432 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284262931659 : ℝ) / (2 * 0.560491187266 * 111.498878918130)) * 0.163000595063 +
        0.284262931659 ^ 2 / (2 * 0.560491187266 * 111.498878918130) := by gcongr
    _ ≤ (0.164017813984 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053457952646) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411191542)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284262931659) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12432 12432 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491187266 : ℝ) ≤ plow 12432 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.498878918130 : ℝ) ≤ √(12432 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12432 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12432 Θ 1.22 ≤ 0.011893397610 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.498878918130 := by gcongr <;> linarith
      _ ≤ (0.011893397610 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12432 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12432 12432 0.011 ≤ 0.008573064748 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12432 12432 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12432 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12432 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12432 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12432 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164017813984 + 0.011893397610 + (0.008573064748 : ℝ) *
        (1 + 2 * (0.284262931659 + 0.011893397610) / (0.560491187266 * 111.498878918130))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12432]

end BstLean.Part269.N12432

/-! The original eight local profiles supply actual 12432 moment certificates. -/
namespace BstLean.Part269.N12432
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12432 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12432 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12432 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053457952646 ∧
    0 ≤ bN 12432 BstLean.Part154.csC (groupTheta g) ∧ bN 12432 BstLean.Part154.csC (groupTheta g) ≤ 0.001411191542 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12432 12432 0.011
      (momentAllowance 12432 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12432 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12432 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12432 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12432 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12432 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231209758977 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12432 0.011
      (momentAllowance 12432 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12432 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12432
/-! The actual computed-centre upper energy formula at 12432. -/
namespace BstLean.Part269.N12432
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12432

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12432
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12432)
open BstLean.Part268 (cell12432)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086314599684
  | 2 => 0.087273509003
  | 3 => 0.088233075051
  | 4 => 0.089195283229
  | 5 => 0.090162514072
  | 6 => 0.091137599158
  | 7 => 0.092123881767
  | 8 => 0.093125282254
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12432 12432 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12432 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12432

/-! Actual upper energy certificates on all 43 source endpoints at 12432. -/
namespace BstLean.Part269.N12432
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12432)
open BstLean.Part268 (cell12432)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12432 (gMinus 12432) (1 - (cell12432 i).lower) ≤ 1 ∧
    energyUpper 12432 (gMinus 12432) (BstLean.Part211.gPlus 12432)
      (finiteEnergy 12432 12432 0.011) (1 - (cell12432 i).lower) ≤
      (cell12432 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨10,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨11,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨12,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨13,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨14,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨15,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨16,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨17,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨18,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨19,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨20,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨21,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨22,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨23,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨24,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨25,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨26,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨27,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨28,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨29,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨30,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨31,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨32,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨33,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨34,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨35,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨36,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨37,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨38,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨39,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨40,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨41,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨42,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨43,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨44,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨45,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨46,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨47,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨48,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨49,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨50,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨51,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12432) (by norm_num)
        (q := 1 - (cell12432 ⟨52,by decide⟩).lower)
        (by norm_num [cell12432]) (by norm_num [cell12432])
      exact ⟨E.1,E.2.trans (by norm_num [cell12432])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12432

/-! Source-cell containment and simple scalar guards at 12432. -/
namespace BstLean.Part269.N12432
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12432)
open BstLean.Part268 (cell12432)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12432 ⟨10,by decide⟩).lower ∧ (cell12432 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12432 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12432 ⟨11,by decide⟩).lower ∧ (cell12432 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12432 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12432 ⟨12,by decide⟩).lower ∧ (cell12432 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12432 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12432 ⟨13,by decide⟩).lower ∧ (cell12432 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12432 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12432 ⟨14,by decide⟩).lower ∧ (cell12432 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12432 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12432 ⟨15,by decide⟩).lower ∧ (cell12432 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12432 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12432 ⟨16,by decide⟩).lower ∧ (cell12432 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12432 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12432 ⟨17,by decide⟩).lower ∧ (cell12432 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12432 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12432 ⟨18,by decide⟩).lower ∧ (cell12432 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12432 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12432 ⟨19,by decide⟩).lower ∧ (cell12432 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12432 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12432 ⟨20,by decide⟩).lower ∧ (cell12432 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12432 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12432 ⟨21,by decide⟩).lower ∧ (cell12432 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12432 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12432 ⟨22,by decide⟩).lower ∧ (cell12432 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12432 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12432 ⟨23,by decide⟩).lower ∧ (cell12432 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12432 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12432 ⟨24,by decide⟩).lower ∧ (cell12432 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12432 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12432 ⟨25,by decide⟩).lower ∧ (cell12432 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12432 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12432 ⟨26,by decide⟩).lower ∧ (cell12432 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12432 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12432 ⟨27,by decide⟩).lower ∧ (cell12432 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12432 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12432 ⟨28,by decide⟩).lower ∧ (cell12432 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12432 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12432 ⟨29,by decide⟩).lower ∧ (cell12432 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12432 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12432 ⟨30,by decide⟩).lower ∧ (cell12432 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12432 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12432 ⟨31,by decide⟩).lower ∧ (cell12432 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12432 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12432 ⟨32,by decide⟩).lower ∧ (cell12432 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12432 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12432 ⟨33,by decide⟩).lower ∧ (cell12432 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12432 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12432 ⟨34,by decide⟩).lower ∧ (cell12432 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12432 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12432 ⟨35,by decide⟩).lower ∧ (cell12432 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12432 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12432 ⟨36,by decide⟩).lower ∧ (cell12432 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12432 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12432 ⟨37,by decide⟩).lower ∧ (cell12432 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12432 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12432 ⟨38,by decide⟩).lower ∧ (cell12432 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12432 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12432 ⟨39,by decide⟩).lower ∧ (cell12432 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12432 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12432 ⟨40,by decide⟩).lower ∧ (cell12432 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12432 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12432 ⟨41,by decide⟩).lower ∧ (cell12432 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12432 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12432 ⟨42,by decide⟩).lower ∧ (cell12432 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12432 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12432 ⟨43,by decide⟩).lower ∧ (cell12432 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12432 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12432 ⟨44,by decide⟩).lower ∧ (cell12432 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12432 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12432 ⟨45,by decide⟩).lower ∧ (cell12432 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12432 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12432 ⟨46,by decide⟩).lower ∧ (cell12432 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12432 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12432 ⟨47,by decide⟩).lower ∧ (cell12432 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12432 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12432 ⟨48,by decide⟩).lower ∧ (cell12432 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12432 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12432 ⟨49,by decide⟩).lower ∧ (cell12432 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12432 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12432 ⟨50,by decide⟩).lower ∧ (cell12432 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12432 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12432 ⟨51,by decide⟩).lower ∧ (cell12432 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12432 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12432 ⟨52,by decide⟩).lower ∧ (cell12432 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12432 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12432 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12432 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12432,cell12432,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12432 i).lower ∧
    (cell12432 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12432 i).upper ≤ (0.532 : ℝ) ∧
    (cell12432 i).centre ≤ (0.1 : ℝ) ∧ (cell12432 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12432 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12432 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12432

/-! The local source numeric instances at 12432 have no network premises. -/
namespace BstLean.Part269.N12432
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12432)
open BstLean.Part268 (cell12432)

noncomputable def sourceNumerics12432 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12432 (cell12432 i)
      scalarRow12432.M scalarRow12432.H scalarRow12432.xi := by
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
    energy_allowance := scalarRow12432.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12432]
    centre_nonneg := (scalarRow12432.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12432])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12432
/-! Actual 12433 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12433
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12433 ≤ (1.036195081856 : ℝ) := by
  have hr : (111.503363177977 : ℝ) ≤ √(12433 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.503363177977 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12433 12433 (11 / 1000) ≤
    (0.008572719968 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12433) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.503363177977 : ℝ) ≤ √(12433 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12433)
  have hdiv : K / √(12433 : ℝ) ≤ K / 111.503363177977 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.503363177977 ≤ (0.008572719968 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12433.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12433 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12433 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12433 := gPlus_lower 12433
end BstLean.Part269.N12433

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12433
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036195081855 : ℝ) ≤ wn 12433 := by
  have hn : √(12433 : ℝ) ≤ 111.503363177978 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12433 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.503363177978 ≤ 2 / √(12433 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257385883 : ℝ) ≤ rhoBar 12433 BstLean.Part154.csC ∧
    rhoBar 12433 BstLean.Part154.csC ≤ 0.000257386282 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036195081855 : ℝ) / (1.295212 * 12433) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036195081856 : ℝ) / (1.29521 * 12433) := by gcongr
      _ ≤ (0.000257386282 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12433 BstLean.Part154.csC) ≤ 0.001029611376 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12433 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12433 BstLean.Part154.csC) (piBar (rhoBar 12433 BstLean.Part154.csC)) ≤ 0.000196593578 ∧
    cc1 (rhoBar 12433 BstLean.Part154.csC) (piBar (rhoBar 12433 BstLean.Part154.csC)) ≤ 0.000125093758 ∧
    cc2 (rhoBar 12433 BstLean.Part154.csC) ≤ 0.000072617835 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12433 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12433 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12433 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12433 BstLean.Part154.csC * nuR (rhoBar 12433 BstLean.Part154.csC)) ≤ 0.000514789126 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257386282 : ℝ) * 0.001029611376 := by gcongr
      _ ≤ (0.000514789126 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12433 BstLean.Part154.csC) * nuR (rhoBar 12433 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001029611376 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12433 BstLean.Part154.csC) * rhoBar 12433 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257386282 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257386282 / 2 + 0.399 * 0.001029611376 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196593578 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514789126 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125093758 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257386282 / 1.414213562 := by gcongr
      _ ≤ (0.000072617835 : ℝ) := by norm_num

end BstLean.Part269.N12433

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12433
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12433 BstLean.Part154.csC) (piBar (rhoBar 12433 BstLean.Part154.csC)) ≤ 1.66907E-7 := by
  have hr0 : 0 ≤ rhoBar 12433 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12433 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12433 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12433 BstLean.Part154.csC) (piBar (rhoBar 12433 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12433 BstLean.Part154.csC) (piBar (rhoBar 12433 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12433 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196593578 : ℝ) ^ 2 + 0.000125093758 ^ 2 + 3 * 0.000072617835 ^ 2 +
        2 * 0.797885 * 0.000196593578 * 0.000125093758 + 2 * 0.000196593578 * 0.000072617835 +
        4 * 0.797885 * 0.000125093758 * 0.000072617835 := by gcongr
    _ ≤ (1.66907E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12433 BstLean.Part154.csC Θ ≤ 0.002687765320 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12433 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12433 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12433 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12433 BstLean.Part154.csC) (piBar (rhoBar 12433 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12433 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036195081856 * 1.66907E-7 / (0.000257385883 : ℝ) := by gcongr
    _ ≤ 0.002687765320 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12433 BstLean.Part154.csC Θ ≤ 0.002983323829 + 0.000679152225 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12433 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12433 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12433 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036195081856 : ℝ) * ((2 * Θ * 0.000257386282 +
        (6863 / 10000) * 0.000257386282 * 12433 * 0.001029611376) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002983323829 + 0.000679152225 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12433 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12433 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12433 0.011 Θ ∧ gammaRatio 12433 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12433 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036195081856 : ℝ) * 0.525 / ((1 - 0.011) * 12433) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12433 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12433 0.011 Θ) :=
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
    badAllowance 12433 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12433 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12433 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12433 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12433 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12433 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12433 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12433 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12433 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12433 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12433 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036195081856 : ℝ) * 12433 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12433 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004183323829 + 0.003366917545 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12433

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12433
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12433 BstLean.Part154.csC) (piBar (rhoBar 12433 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12433 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12433 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12433 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12433 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12433 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12433 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12433 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12433 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12433 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12433 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12433 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12433 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12433 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12433 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053051015700 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12433) ≤ 0.010710327896 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12433 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036195081856)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010710327896 + 2 * 0.737676 / 12433) := by gcongr
    _ ≤ (0.053051015700 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12433 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12433

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12433
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491234456 : ℝ) ≤ plow 12433 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12433) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053457555541)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411076793) : eMP 12433 0.011 xi bn ≤ 0.001214522939 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12433 : ℝ) * (1 - 0.011))) ≤ 0.000600432474 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001411076793 / (12433 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000600432474 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000600432474 : ℝ) + 3.141593 * 0.053457555541 / (12433 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001214522939 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053457555541)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411076793) : PiBarMP 12433 12 0.011 xi bn ≤ 0.162994015799 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12433 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037564302110 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.888398852179 : ℝ) ≤ √((12433 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.503363177977 : ℝ) ≤ √(12433 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12433) ≤ 0.124950565308 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037564302110 + 0.053457555541 * 1.772454 / (2 * (110.888398852179 : ℝ))) * (1 + 0.001214522939) +
        8 / (12433 * 111.503363177977) + 0.124950565308 := by gcongr
    _ ≤ (0.162994015799 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053457555541)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411076793) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284259915921) :
    parallelOracle 12433 0.011 xi bn cd ≤ 0.164011161114 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12433 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12433 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491234456 : ℝ) ≤ plow 12433 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.503363177977 : ℝ) ≤ √(12433 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284259915921 : ℝ) / (2 * 0.560491234456 * 111.503363177977)) * 0.162994015799 +
        0.284259915921 ^ 2 / (2 * 0.560491234456 * 111.503363177977) := by gcongr
    _ ≤ (0.164011161114 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053457555541) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001411076793)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284259915921) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12433 12433 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491234456 : ℝ) ≤ plow 12433 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.503363177977 : ℝ) ≤ √(12433 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12433 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12433 Θ 1.22 ≤ 0.011892919301 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.503363177977 := by gcongr <;> linarith
      _ ≤ (0.011892919301 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12433 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12433 12433 0.011 ≤ 0.008572719968 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12433 12433 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12433 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12433 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12433 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12433 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164011161114 + 0.011892919301 + (0.008572719968 : ℝ) *
        (1 + 2 * (0.284259915921 + 0.011892919301) / (0.560491234456 * 111.503363177977))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12433]

end BstLean.Part269.N12433

/-! The original eight local profiles supply actual 12433 moment certificates. -/
namespace BstLean.Part269.N12433
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12433 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12433 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12433 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053457555541 ∧
    0 ≤ bN 12433 BstLean.Part154.csC (groupTheta g) ∧ bN 12433 BstLean.Part154.csC (groupTheta g) ≤ 0.001411076793 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12433 12433 0.011
      (momentAllowance 12433 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12433 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12433 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12433 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12433 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12433 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231208900221 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12433 0.011
      (momentAllowance 12433 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12433 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12433
/-! The actual computed-centre upper energy formula at 12433. -/
namespace BstLean.Part269.N12433
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12433

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12433
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12433)
open BstLean.Part268 (cell12433)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086311349199
  | 2 => 0.087270190699
  | 3 => 0.088229677778
  | 4 => 0.089191793369
  | 5 => 0.090158915127
  | 6 => 0.091133871279
  | 7 => 0.092120001240
  | 8 => 0.093121220932
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12433 12433 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12433 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12433

/-! Actual upper energy certificates on all 43 source endpoints at 12433. -/
namespace BstLean.Part269.N12433
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12433)
open BstLean.Part268 (cell12433)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12433 (gMinus 12433) (1 - (cell12433 i).lower) ≤ 1 ∧
    energyUpper 12433 (gMinus 12433) (BstLean.Part211.gPlus 12433)
      (finiteEnergy 12433 12433 0.011) (1 - (cell12433 i).lower) ≤
      (cell12433 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨10,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨11,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨12,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨13,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨14,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨15,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨16,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨17,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨18,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨19,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨20,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨21,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨22,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨23,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨24,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨25,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨26,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨27,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨28,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨29,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨30,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨31,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨32,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨33,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨34,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨35,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨36,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨37,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨38,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨39,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨40,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨41,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨42,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨43,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨44,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨45,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨46,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨47,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨48,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨49,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨50,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨51,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12433) (by norm_num)
        (q := 1 - (cell12433 ⟨52,by decide⟩).lower)
        (by norm_num [cell12433]) (by norm_num [cell12433])
      exact ⟨E.1,E.2.trans (by norm_num [cell12433])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12433

/-! Source-cell containment and simple scalar guards at 12433. -/
namespace BstLean.Part269.N12433
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12433)
open BstLean.Part268 (cell12433)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12433 ⟨10,by decide⟩).lower ∧ (cell12433 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12433 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12433 ⟨11,by decide⟩).lower ∧ (cell12433 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12433 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12433 ⟨12,by decide⟩).lower ∧ (cell12433 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12433 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12433 ⟨13,by decide⟩).lower ∧ (cell12433 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12433 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12433 ⟨14,by decide⟩).lower ∧ (cell12433 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12433 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12433 ⟨15,by decide⟩).lower ∧ (cell12433 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12433 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12433 ⟨16,by decide⟩).lower ∧ (cell12433 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12433 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12433 ⟨17,by decide⟩).lower ∧ (cell12433 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12433 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12433 ⟨18,by decide⟩).lower ∧ (cell12433 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12433 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12433 ⟨19,by decide⟩).lower ∧ (cell12433 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12433 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12433 ⟨20,by decide⟩).lower ∧ (cell12433 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12433 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12433 ⟨21,by decide⟩).lower ∧ (cell12433 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12433 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12433 ⟨22,by decide⟩).lower ∧ (cell12433 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12433 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12433 ⟨23,by decide⟩).lower ∧ (cell12433 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12433 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12433 ⟨24,by decide⟩).lower ∧ (cell12433 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12433 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12433 ⟨25,by decide⟩).lower ∧ (cell12433 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12433 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12433 ⟨26,by decide⟩).lower ∧ (cell12433 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12433 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12433 ⟨27,by decide⟩).lower ∧ (cell12433 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12433 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12433 ⟨28,by decide⟩).lower ∧ (cell12433 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12433 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12433 ⟨29,by decide⟩).lower ∧ (cell12433 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12433 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12433 ⟨30,by decide⟩).lower ∧ (cell12433 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12433 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12433 ⟨31,by decide⟩).lower ∧ (cell12433 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12433 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12433 ⟨32,by decide⟩).lower ∧ (cell12433 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12433 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12433 ⟨33,by decide⟩).lower ∧ (cell12433 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12433 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12433 ⟨34,by decide⟩).lower ∧ (cell12433 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12433 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12433 ⟨35,by decide⟩).lower ∧ (cell12433 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12433 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12433 ⟨36,by decide⟩).lower ∧ (cell12433 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12433 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12433 ⟨37,by decide⟩).lower ∧ (cell12433 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12433 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12433 ⟨38,by decide⟩).lower ∧ (cell12433 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12433 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12433 ⟨39,by decide⟩).lower ∧ (cell12433 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12433 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12433 ⟨40,by decide⟩).lower ∧ (cell12433 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12433 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12433 ⟨41,by decide⟩).lower ∧ (cell12433 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12433 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12433 ⟨42,by decide⟩).lower ∧ (cell12433 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12433 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12433 ⟨43,by decide⟩).lower ∧ (cell12433 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12433 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12433 ⟨44,by decide⟩).lower ∧ (cell12433 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12433 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12433 ⟨45,by decide⟩).lower ∧ (cell12433 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12433 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12433 ⟨46,by decide⟩).lower ∧ (cell12433 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12433 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12433 ⟨47,by decide⟩).lower ∧ (cell12433 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12433 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12433 ⟨48,by decide⟩).lower ∧ (cell12433 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12433 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12433 ⟨49,by decide⟩).lower ∧ (cell12433 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12433 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12433 ⟨50,by decide⟩).lower ∧ (cell12433 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12433 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12433 ⟨51,by decide⟩).lower ∧ (cell12433 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12433 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12433 ⟨52,by decide⟩).lower ∧ (cell12433 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12433 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12433 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12433 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12433,cell12433,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12433 i).lower ∧
    (cell12433 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12433 i).upper ≤ (0.532 : ℝ) ∧
    (cell12433 i).centre ≤ (0.1 : ℝ) ∧ (cell12433 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12433 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12433 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12433

/-! The local source numeric instances at 12433 have no network premises. -/
namespace BstLean.Part269.N12433
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12433)
open BstLean.Part268 (cell12433)

noncomputable def sourceNumerics12433 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12433 (cell12433 i)
      scalarRow12433.M scalarRow12433.H scalarRow12433.xi := by
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
    energy_allowance := scalarRow12433.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12433]
    centre_nonneg := (scalarRow12433.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12433])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12433
/-! Actual 12434 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12434
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12434 ≤ (1.036193613402 : ℝ) := by
  have hr : (111.507847257491 : ℝ) ≤ √(12434 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.507847257491 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12434 12434 (11 / 1000) ≤
    (0.008572375230 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12434) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.507847257491 : ℝ) ≤ √(12434 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12434)
  have hdiv : K / √(12434 : ℝ) ≤ K / 111.507847257491 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.507847257491 ≤ (0.008572375230 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12434.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12434 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12434 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12434 := gPlus_lower 12434
end BstLean.Part269.N12434

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12434
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036193613401 : ℝ) ≤ wn 12434 := by
  have hn : √(12434 : ℝ) ≤ 111.507847257492 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12434 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.507847257492 ≤ 2 / √(12434 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257364819 : ℝ) ≤ rhoBar 12434 BstLean.Part154.csC ∧
    rhoBar 12434 BstLean.Part154.csC ≤ 0.000257365217 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036193613401 : ℝ) / (1.295212 * 12434) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036193613402 : ℝ) / (1.29521 * 12434) := by gcongr
      _ ≤ (0.000257365217 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12434 BstLean.Part154.csC) ≤ 0.001029527105 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12434 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12434 BstLean.Part154.csC) (piBar (rhoBar 12434 BstLean.Part154.csC)) ≤ 0.000196577488 ∧
    cc1 (rhoBar 12434 BstLean.Part154.csC) (piBar (rhoBar 12434 BstLean.Part154.csC)) ≤ 0.000125083520 ∧
    cc2 (rhoBar 12434 BstLean.Part154.csC) ≤ 0.000072611892 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12434 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12434 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12434 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12434 BstLean.Part154.csC * nuR (rhoBar 12434 BstLean.Part154.csC)) ≤ 0.000514746993 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257365217 : ℝ) * 0.001029527105 := by gcongr
      _ ≤ (0.000514746993 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12434 BstLean.Part154.csC) * nuR (rhoBar 12434 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001029527105 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12434 BstLean.Part154.csC) * rhoBar 12434 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257365217 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257365217 / 2 + 0.399 * 0.001029527105 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196577488 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514746993 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125083520 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257365217 / 1.414213562 := by gcongr
      _ ≤ (0.000072611892 : ℝ) := by norm_num

end BstLean.Part269.N12434

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12434
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12434 BstLean.Part154.csC) (piBar (rhoBar 12434 BstLean.Part154.csC)) ≤ 1.66879E-7 := by
  have hr0 : 0 ≤ rhoBar 12434 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12434 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12434 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12434 BstLean.Part154.csC) (piBar (rhoBar 12434 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12434 BstLean.Part154.csC) (piBar (rhoBar 12434 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12434 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196577488 : ℝ) ^ 2 + 0.000125083520 ^ 2 + 3 * 0.000072611892 ^ 2 +
        2 * 0.797885 * 0.000196577488 * 0.000125083520 + 2 * 0.000196577488 * 0.000072611892 +
        4 * 0.797885 * 0.000125083520 * 0.000072611892 := by gcongr
    _ ≤ (1.66879E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12434 BstLean.Part154.csC Θ ≤ 0.002687530560 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12434 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12434 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12434 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12434 BstLean.Part154.csC) (piBar (rhoBar 12434 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12434 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036193613402 * 1.66879E-7 / (0.000257364819 : ℝ) := by gcongr
    _ ≤ 0.002687530560 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12434 BstLean.Part154.csC Θ ≤ 0.002983071196 + 0.000679095680 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12434 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12434 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12434 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036193613402 : ℝ) * ((2 * Θ * 0.000257365217 +
        (6863 / 10000) * 0.000257365217 * 12434 * 0.001029527105) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002983071196 + 0.000679095680 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12434 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12434 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12434 0.011 Θ ∧ gammaRatio 12434 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12434 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036193613402 : ℝ) * 0.525 / ((1 - 0.011) * 12434) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12434 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12434 0.011 Θ) :=
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
    badAllowance 12434 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12434 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12434 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12434 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12434 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12434 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12434 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12434 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12434 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12434 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12434 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036193613402 : ℝ) * 12434 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12434 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004183071196 + 0.003366626240 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12434

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12434
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12434 BstLean.Part154.csC) (piBar (rhoBar 12434 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12434 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12434 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12434 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12434 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12434 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12434 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12434 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12434 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12434 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12434 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12434 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12434 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12434 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12434 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053048858975 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12434) ≤ 0.010709897200 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12434 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036193613402)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010709897200 + 2 * 0.737676 / 12434) := by gcongr
    _ ≤ (0.053048858975 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12434 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12434

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12434
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491281639 : ℝ) ≤ plow 12434 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12434) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053457149972)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410953544) : eMP 12434 0.011 xi bn ≤ 0.001214421002 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12434 : ℝ) * (1 - 0.011))) ≤ 0.000600382107 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001410953544 / (12434 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000600382107 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000600382107 : ℝ) + 3.141593 * 0.053457149972 / (12434 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001214421002 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053457149972)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410953544) : PiBarMP 12434 12 0.011 xi bn ≤ 0.162987323597 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12434 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037562661568 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.892858201058 : ℝ) ≤ √((12434 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.507847257491 : ℝ) ≤ √(12434 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12434) ≤ 0.124945540655 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037562661568 + 0.053457149972 * 1.772454 / (2 * (110.892858201058 : ℝ))) * (1 + 0.001214421002) +
        8 / (12434 * 111.507847257491) + 0.124945540655 := by gcongr
    _ ≤ (0.162987323597 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053457149972)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410953544) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284256882132) :
    parallelOracle 12434 0.011 xi bn cd ≤ 0.164004394951 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12434 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12434 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491281639 : ℝ) ≤ plow 12434 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.507847257491 : ℝ) ≤ √(12434 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284256882132 : ℝ) / (2 * 0.560491281639 * 111.507847257491)) * 0.162987323597 +
        0.284256882132 ^ 2 / (2 * 0.560491281639 * 111.507847257491) := by gcongr
    _ ≤ (0.164004394951 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053457149972) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410953544)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284256882132) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12434 12434 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491281639 : ℝ) ≤ plow 12434 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.507847257491 : ℝ) ≤ √(12434 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12434 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12434 Θ 1.22 ≤ 0.011892441049 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.507847257491 := by gcongr <;> linarith
      _ ≤ (0.011892441049 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12434 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12434 12434 0.011 ≤ 0.008572375230 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12434 12434 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12434 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12434 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12434 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12434 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164004394951 + 0.011892441049 + (0.008572375230 : ℝ) *
        (1 + 2 * (0.284256882132 + 0.011892441049) / (0.560491281639 * 111.507847257491))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12434]

end BstLean.Part269.N12434

/-! The original eight local profiles supply actual 12434 moment certificates. -/
namespace BstLean.Part269.N12434
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12434 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12434 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12434 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053457149972 ∧
    0 ≤ bN 12434 BstLean.Part154.csC (groupTheta g) ∧ bN 12434 BstLean.Part154.csC (groupTheta g) ≤ 0.001410953544 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12434 12434 0.011
      (momentAllowance 12434 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12434 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12434 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12434 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12434 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12434 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231208023157 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12434 0.011
      (momentAllowance 12434 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12434 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12434
/-! The actual computed-centre upper energy formula at 12434. -/
namespace BstLean.Part269.N12434
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12434

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12434
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12434)
open BstLean.Part268 (cell12434)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086308100148
  | 2 => 0.087266873893
  | 3 => 0.088226282080
  | 4 => 0.089188305180
  | 5 => 0.090155317968
  | 6 => 0.091130145327
  | 7 => 0.092116122810
  | 8 => 0.093117161910
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12434 12434 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12434 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12434

/-! Actual upper energy certificates on all 43 source endpoints at 12434. -/
namespace BstLean.Part269.N12434
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12434)
open BstLean.Part268 (cell12434)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12434 (gMinus 12434) (1 - (cell12434 i).lower) ≤ 1 ∧
    energyUpper 12434 (gMinus 12434) (BstLean.Part211.gPlus 12434)
      (finiteEnergy 12434 12434 0.011) (1 - (cell12434 i).lower) ≤
      (cell12434 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨10,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨11,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨12,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨13,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨14,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨15,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨16,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨17,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨18,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨19,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨20,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨21,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨22,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨23,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨24,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨25,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨26,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨27,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨28,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨29,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨30,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨31,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨32,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨33,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨34,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨35,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨36,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨37,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨38,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨39,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨40,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨41,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨42,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨43,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨44,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨45,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨46,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨47,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨48,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨49,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨50,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨51,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12434) (by norm_num)
        (q := 1 - (cell12434 ⟨52,by decide⟩).lower)
        (by norm_num [cell12434]) (by norm_num [cell12434])
      exact ⟨E.1,E.2.trans (by norm_num [cell12434])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12434

/-! Source-cell containment and simple scalar guards at 12434. -/
namespace BstLean.Part269.N12434
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12434)
open BstLean.Part268 (cell12434)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12434 ⟨10,by decide⟩).lower ∧ (cell12434 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12434 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12434 ⟨11,by decide⟩).lower ∧ (cell12434 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12434 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12434 ⟨12,by decide⟩).lower ∧ (cell12434 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12434 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12434 ⟨13,by decide⟩).lower ∧ (cell12434 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12434 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12434 ⟨14,by decide⟩).lower ∧ (cell12434 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12434 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12434 ⟨15,by decide⟩).lower ∧ (cell12434 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12434 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12434 ⟨16,by decide⟩).lower ∧ (cell12434 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12434 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12434 ⟨17,by decide⟩).lower ∧ (cell12434 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12434 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12434 ⟨18,by decide⟩).lower ∧ (cell12434 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12434 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12434 ⟨19,by decide⟩).lower ∧ (cell12434 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12434 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12434 ⟨20,by decide⟩).lower ∧ (cell12434 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12434 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12434 ⟨21,by decide⟩).lower ∧ (cell12434 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12434 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12434 ⟨22,by decide⟩).lower ∧ (cell12434 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12434 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12434 ⟨23,by decide⟩).lower ∧ (cell12434 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12434 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12434 ⟨24,by decide⟩).lower ∧ (cell12434 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12434 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12434 ⟨25,by decide⟩).lower ∧ (cell12434 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12434 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12434 ⟨26,by decide⟩).lower ∧ (cell12434 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12434 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12434 ⟨27,by decide⟩).lower ∧ (cell12434 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12434 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12434 ⟨28,by decide⟩).lower ∧ (cell12434 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12434 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12434 ⟨29,by decide⟩).lower ∧ (cell12434 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12434 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12434 ⟨30,by decide⟩).lower ∧ (cell12434 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12434 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12434 ⟨31,by decide⟩).lower ∧ (cell12434 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12434 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12434 ⟨32,by decide⟩).lower ∧ (cell12434 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12434 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12434 ⟨33,by decide⟩).lower ∧ (cell12434 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12434 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12434 ⟨34,by decide⟩).lower ∧ (cell12434 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12434 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12434 ⟨35,by decide⟩).lower ∧ (cell12434 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12434 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12434 ⟨36,by decide⟩).lower ∧ (cell12434 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12434 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12434 ⟨37,by decide⟩).lower ∧ (cell12434 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12434 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12434 ⟨38,by decide⟩).lower ∧ (cell12434 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12434 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12434 ⟨39,by decide⟩).lower ∧ (cell12434 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12434 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12434 ⟨40,by decide⟩).lower ∧ (cell12434 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12434 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12434 ⟨41,by decide⟩).lower ∧ (cell12434 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12434 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12434 ⟨42,by decide⟩).lower ∧ (cell12434 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12434 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12434 ⟨43,by decide⟩).lower ∧ (cell12434 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12434 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12434 ⟨44,by decide⟩).lower ∧ (cell12434 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12434 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12434 ⟨45,by decide⟩).lower ∧ (cell12434 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12434 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12434 ⟨46,by decide⟩).lower ∧ (cell12434 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12434 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12434 ⟨47,by decide⟩).lower ∧ (cell12434 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12434 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12434 ⟨48,by decide⟩).lower ∧ (cell12434 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12434 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12434 ⟨49,by decide⟩).lower ∧ (cell12434 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12434 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12434 ⟨50,by decide⟩).lower ∧ (cell12434 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12434 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12434 ⟨51,by decide⟩).lower ∧ (cell12434 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12434 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12434 ⟨52,by decide⟩).lower ∧ (cell12434 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12434 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12434 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12434 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12434,cell12434,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12434 i).lower ∧
    (cell12434 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12434 i).upper ≤ (0.532 : ℝ) ∧
    (cell12434 i).centre ≤ (0.1 : ℝ) ∧ (cell12434 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12434 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12434 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12434

/-! The local source numeric instances at 12434 have no network premises. -/
namespace BstLean.Part269.N12434
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12434)
open BstLean.Part268 (cell12434)

noncomputable def sourceNumerics12434 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12434 (cell12434 i)
      scalarRow12434.M scalarRow12434.H scalarRow12434.xi := by
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
    energy_allowance := scalarRow12434.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12434]
    centre_nonneg := (scalarRow12434.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12434])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12434
/-! Actual 12435 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12435
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12435 ≤ (1.036192145125 : ℝ) := by
  have hr : (111.512331156693 : ℝ) ≤ √(12435 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.512331156693 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12435 12435 (11 / 1000) ≤
    (0.008572030533 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12435) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.512331156693 : ℝ) ≤ √(12435 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12435)
  have hdiv : K / √(12435 : ℝ) ≤ K / 111.512331156693 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.512331156693 ≤ (0.008572030533 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12435.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12435 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12435 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12435 := gPlus_lower 12435
end BstLean.Part269.N12435

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12435
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036192145124 : ℝ) ≤ wn 12435 := by
  have hn : √(12435 : ℝ) ≤ 111.512331156694 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12435 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.512331156694 ≤ 2 / √(12435 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257343757 : ℝ) ≤ rhoBar 12435 BstLean.Part154.csC ∧
    rhoBar 12435 BstLean.Part154.csC ≤ 0.000257344156 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036192145124 : ℝ) / (1.295212 * 12435) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036192145125 : ℝ) / (1.29521 * 12435) := by gcongr
      _ ≤ (0.000257344156 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12435 BstLean.Part154.csC) ≤ 0.001029442851 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12435 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12435 BstLean.Part154.csC) (piBar (rhoBar 12435 BstLean.Part154.csC)) ≤ 0.000196561401 ∧
    cc1 (rhoBar 12435 BstLean.Part154.csC) (piBar (rhoBar 12435 BstLean.Part154.csC)) ≤ 0.000125073284 ∧
    cc2 (rhoBar 12435 BstLean.Part154.csC) ≤ 0.000072605950 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12435 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12435 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12435 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12435 BstLean.Part154.csC * nuR (rhoBar 12435 BstLean.Part154.csC)) ≤ 0.000514704869 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257344156 : ℝ) * 0.001029442851 := by gcongr
      _ ≤ (0.000514704869 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12435 BstLean.Part154.csC) * nuR (rhoBar 12435 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001029442851 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12435 BstLean.Part154.csC) * rhoBar 12435 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257344156 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257344156 / 2 + 0.399 * 0.001029442851 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196561401 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514704869 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125073284 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257344156 / 1.414213562 := by gcongr
      _ ≤ (0.000072605950 : ℝ) := by norm_num

end BstLean.Part269.N12435

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12435
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12435 BstLean.Part154.csC) (piBar (rhoBar 12435 BstLean.Part154.csC)) ≤ 1.66852E-7 := by
  have hr0 : 0 ≤ rhoBar 12435 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12435 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12435 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12435 BstLean.Part154.csC) (piBar (rhoBar 12435 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12435 BstLean.Part154.csC) (piBar (rhoBar 12435 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12435 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196561401 : ℝ) ^ 2 + 0.000125073284 ^ 2 + 3 * 0.000072605950 ^ 2 +
        2 * 0.797885 * 0.000196561401 * 0.000125073284 + 2 * 0.000196561401 * 0.000072605950 +
        4 * 0.797885 * 0.000125073284 * 0.000072605950 := by gcongr
    _ ≤ (1.66852E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12435 BstLean.Part154.csC Θ ≤ 0.002687311848 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12435 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12435 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12435 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12435 BstLean.Part154.csC) (piBar (rhoBar 12435 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12435 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036192145125 * 1.66852E-7 / (0.000257343757 : ℝ) := by gcongr
    _ ≤ 0.002687311848 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12435 BstLean.Part154.csC Θ ≤ 0.002982818621 + 0.000679039145 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12435 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12435 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12435 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036192145125 : ℝ) * ((2 * Θ * 0.000257344156 +
        (6863 / 10000) * 0.000257344156 * 12435 * 0.001029442851) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002982818621 + 0.000679039145 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12435 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12435 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12435 0.011 Θ ∧ gammaRatio 12435 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12435 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036192145125 : ℝ) * 0.525 / ((1 - 0.011) * 12435) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12435 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12435 0.011 Θ) :=
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
    badAllowance 12435 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12435 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12435 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12435 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12435 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12435 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12435 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12435 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12435 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12435 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12435 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036192145125 : ℝ) * 12435 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12435 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004182818621 + 0.003366350993 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12435

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12435
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12435 BstLean.Part154.csC) (piBar (rhoBar 12435 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12435 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12435 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12435 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12435 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12435 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12435 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12435 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12435 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12435 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12435 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12435 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12435 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12435 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12435 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053046702513 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12435) ≤ 0.010709466556 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12435 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036192145125)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010709466556 + 2 * 0.737676 / 12435) := by gcongr
    _ ≤ (0.053046702513 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12435 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12435

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12435
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491328813 : ℝ) ≤ plow 12435 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12435) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053456752893)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410838721) : eMP 12435 0.011 xi bn ≤ 0.001214322663 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12435 : ℝ) * (1 - 0.011))) ≤ 0.000600333537 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001410838721 / (12435 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000600333537 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000600333537 : ℝ) + 3.141593 * 0.053456752893 / (12435 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001214322663 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053456752893)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410838721) : PiBarMP 12435 12 0.011 xi bn ≤ 0.162980744433 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12435 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037561133117 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.897317370619 : ℝ) ≤ √((12435 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.512331156693 : ℝ) ≤ √(12435 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12435) ≤ 0.124940516607 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037561133117 + 0.053456752893 * 1.772454 / (2 * (110.897317370619 : ℝ))) * (1 + 0.001214322663) +
        8 / (12435 * 111.512331156693) + 0.124940516607 := by gcongr
    _ ≤ (0.162980744433 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053456752893)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410838721) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284253866963) :
    parallelOracle 12435 0.011 xi bn cd ≤ 0.163997742200 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12435 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12435 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491328813 : ℝ) ≤ plow 12435 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.512331156693 : ℝ) ≤ √(12435 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284253866963 : ℝ) / (2 * 0.560491328813 * 111.512331156693)) * 0.162980744433 +
        0.284253866963 ^ 2 / (2 * 0.560491328813 * 111.512331156693) := by gcongr
    _ ≤ (0.163997742200 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053456752893) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410838721)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284253866963) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12435 12435 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491328813 : ℝ) ≤ plow 12435 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.512331156693 : ℝ) ≤ √(12435 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12435 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12435 Θ 1.22 ≤ 0.011891962856 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.512331156693 := by gcongr <;> linarith
      _ ≤ (0.011891962856 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12435 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12435 12435 0.011 ≤ 0.008572030533 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12435 12435 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12435 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12435 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12435 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12435 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163997742200 + 0.011891962856 + (0.008572030533 : ℝ) *
        (1 + 2 * (0.284253866963 + 0.011891962856) / (0.560491328813 * 111.512331156693))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12435]

end BstLean.Part269.N12435

/-! The original eight local profiles supply actual 12435 moment certificates. -/
namespace BstLean.Part269.N12435
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12435 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12435 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12435 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053456752893 ∧
    0 ≤ bN 12435 BstLean.Part154.csC (groupTheta g) ∧ bN 12435 BstLean.Part154.csC (groupTheta g) ≤ 0.001410838721 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12435 12435 0.011
      (momentAllowance 12435 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12435 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12435 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12435 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12435 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12435 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231207164450 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12435 0.011
      (momentAllowance 12435 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12435 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12435
/-! The actual computed-centre upper energy formula at 12435. -/
namespace BstLean.Part269.N12435
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12435

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12435
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12435)
open BstLean.Part268 (cell12435)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086304852530
  | 2 => 0.087263558582
  | 3 => 0.088222887955
  | 4 => 0.089184818660
  | 5 => 0.090151722594
  | 6 => 0.091126421300
  | 7 => 0.092112246475
  | 8 => 0.093113105187
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12435 12435 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12435 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12435

/-! Actual upper energy certificates on all 43 source endpoints at 12435. -/
namespace BstLean.Part269.N12435
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12435)
open BstLean.Part268 (cell12435)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12435 (gMinus 12435) (1 - (cell12435 i).lower) ≤ 1 ∧
    energyUpper 12435 (gMinus 12435) (BstLean.Part211.gPlus 12435)
      (finiteEnergy 12435 12435 0.011) (1 - (cell12435 i).lower) ≤
      (cell12435 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨10,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨11,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨12,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨13,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨14,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨15,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨16,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨17,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨18,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨19,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨20,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨21,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨22,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨23,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨24,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨25,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨26,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨27,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨28,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨29,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨30,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨31,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨32,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨33,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨34,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨35,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨36,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨37,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨38,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨39,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨40,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨41,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨42,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨43,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨44,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨45,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨46,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨47,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨48,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨49,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨50,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨51,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12435) (by norm_num)
        (q := 1 - (cell12435 ⟨52,by decide⟩).lower)
        (by norm_num [cell12435]) (by norm_num [cell12435])
      exact ⟨E.1,E.2.trans (by norm_num [cell12435])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12435

/-! Source-cell containment and simple scalar guards at 12435. -/
namespace BstLean.Part269.N12435
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12435)
open BstLean.Part268 (cell12435)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12435 ⟨10,by decide⟩).lower ∧ (cell12435 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12435 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12435 ⟨11,by decide⟩).lower ∧ (cell12435 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12435 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12435 ⟨12,by decide⟩).lower ∧ (cell12435 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12435 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12435 ⟨13,by decide⟩).lower ∧ (cell12435 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12435 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12435 ⟨14,by decide⟩).lower ∧ (cell12435 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12435 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12435 ⟨15,by decide⟩).lower ∧ (cell12435 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12435 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12435 ⟨16,by decide⟩).lower ∧ (cell12435 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12435 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12435 ⟨17,by decide⟩).lower ∧ (cell12435 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12435 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12435 ⟨18,by decide⟩).lower ∧ (cell12435 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12435 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12435 ⟨19,by decide⟩).lower ∧ (cell12435 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12435 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12435 ⟨20,by decide⟩).lower ∧ (cell12435 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12435 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12435 ⟨21,by decide⟩).lower ∧ (cell12435 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12435 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12435 ⟨22,by decide⟩).lower ∧ (cell12435 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12435 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12435 ⟨23,by decide⟩).lower ∧ (cell12435 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12435 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12435 ⟨24,by decide⟩).lower ∧ (cell12435 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12435 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12435 ⟨25,by decide⟩).lower ∧ (cell12435 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12435 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12435 ⟨26,by decide⟩).lower ∧ (cell12435 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12435 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12435 ⟨27,by decide⟩).lower ∧ (cell12435 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12435 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12435 ⟨28,by decide⟩).lower ∧ (cell12435 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12435 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12435 ⟨29,by decide⟩).lower ∧ (cell12435 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12435 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12435 ⟨30,by decide⟩).lower ∧ (cell12435 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12435 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12435 ⟨31,by decide⟩).lower ∧ (cell12435 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12435 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12435 ⟨32,by decide⟩).lower ∧ (cell12435 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12435 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12435 ⟨33,by decide⟩).lower ∧ (cell12435 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12435 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12435 ⟨34,by decide⟩).lower ∧ (cell12435 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12435 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12435 ⟨35,by decide⟩).lower ∧ (cell12435 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12435 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12435 ⟨36,by decide⟩).lower ∧ (cell12435 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12435 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12435 ⟨37,by decide⟩).lower ∧ (cell12435 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12435 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12435 ⟨38,by decide⟩).lower ∧ (cell12435 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12435 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12435 ⟨39,by decide⟩).lower ∧ (cell12435 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12435 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12435 ⟨40,by decide⟩).lower ∧ (cell12435 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12435 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12435 ⟨41,by decide⟩).lower ∧ (cell12435 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12435 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12435 ⟨42,by decide⟩).lower ∧ (cell12435 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12435 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12435 ⟨43,by decide⟩).lower ∧ (cell12435 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12435 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12435 ⟨44,by decide⟩).lower ∧ (cell12435 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12435 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12435 ⟨45,by decide⟩).lower ∧ (cell12435 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12435 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12435 ⟨46,by decide⟩).lower ∧ (cell12435 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12435 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12435 ⟨47,by decide⟩).lower ∧ (cell12435 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12435 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12435 ⟨48,by decide⟩).lower ∧ (cell12435 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12435 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12435 ⟨49,by decide⟩).lower ∧ (cell12435 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12435 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12435 ⟨50,by decide⟩).lower ∧ (cell12435 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12435 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12435 ⟨51,by decide⟩).lower ∧ (cell12435 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12435 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12435 ⟨52,by decide⟩).lower ∧ (cell12435 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12435 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12435 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12435 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12435,cell12435,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12435 i).lower ∧
    (cell12435 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12435 i).upper ≤ (0.532 : ℝ) ∧
    (cell12435 i).centre ≤ (0.1 : ℝ) ∧ (cell12435 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12435 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12435 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12435

/-! The local source numeric instances at 12435 have no network premises. -/
namespace BstLean.Part269.N12435
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12435)
open BstLean.Part268 (cell12435)

noncomputable def sourceNumerics12435 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12435 (cell12435 i)
      scalarRow12435.M scalarRow12435.H scalarRow12435.xi := by
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
    energy_allowance := scalarRow12435.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12435]
    centre_nonneg := (scalarRow12435.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12435])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12435
/-! Actual 12436 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12436
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12436 ≤ (1.036190677027 : ℝ) := by
  have hr : (111.516814875605 : ℝ) ≤ √(12436 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.516814875605 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12436 12436 (11 / 1000) ≤
    (0.008571685877 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12436) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.516814875605 : ℝ) ≤ √(12436 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12436)
  have hdiv : K / √(12436 : ℝ) ≤ K / 111.516814875605 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.516814875605 ≤ (0.008571685877 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12436.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12436 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12436 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12436 := gPlus_lower 12436
end BstLean.Part269.N12436

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12436
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036190677026 : ℝ) ≤ wn 12436 := by
  have hn : √(12436 : ℝ) ≤ 111.516814875606 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12436 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.516814875606 ≤ 2 / √(12436 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257322699 : ℝ) ≤ rhoBar 12436 BstLean.Part154.csC ∧
    rhoBar 12436 BstLean.Part154.csC ≤ 0.000257323097 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036190677026 : ℝ) / (1.295212 * 12436) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036190677027 : ℝ) / (1.29521 * 12436) := by gcongr
      _ ≤ (0.000257323097 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12436 BstLean.Part154.csC) ≤ 0.001029358604 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12436 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12436 BstLean.Part154.csC) (piBar (rhoBar 12436 BstLean.Part154.csC)) ≤ 0.000196545315 ∧
    cc1 (rhoBar 12436 BstLean.Part154.csC) (piBar (rhoBar 12436 BstLean.Part154.csC)) ≤ 0.000125063048 ∧
    cc2 (rhoBar 12436 BstLean.Part154.csC) ≤ 0.000072600008 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12436 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12436 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12436 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12436 BstLean.Part154.csC * nuR (rhoBar 12436 BstLean.Part154.csC)) ≤ 0.000514662748 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257323097 : ℝ) * 0.001029358604 := by gcongr
      _ ≤ (0.000514662748 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12436 BstLean.Part154.csC) * nuR (rhoBar 12436 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001029358604 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12436 BstLean.Part154.csC) * rhoBar 12436 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257323097 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257323097 / 2 + 0.399 * 0.001029358604 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196545315 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514662748 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125063048 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257323097 / 1.414213562 := by gcongr
      _ ≤ (0.000072600008 : ℝ) := by norm_num

end BstLean.Part269.N12436

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12436
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12436 BstLean.Part154.csC) (piBar (rhoBar 12436 BstLean.Part154.csC)) ≤ 1.66825E-7 := by
  have hr0 : 0 ≤ rhoBar 12436 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12436 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12436 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12436 BstLean.Part154.csC) (piBar (rhoBar 12436 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12436 BstLean.Part154.csC) (piBar (rhoBar 12436 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12436 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196545315 : ℝ) ^ 2 + 0.000125063048 ^ 2 + 3 * 0.000072600008 ^ 2 +
        2 * 0.797885 * 0.000196545315 * 0.000125063048 + 2 * 0.000196545315 * 0.000072600008 +
        4 * 0.797885 * 0.000125063048 * 0.000072600008 := by gcongr
    _ ≤ (1.66825E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12436 BstLean.Part154.csC Θ ≤ 0.002687093061 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12436 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12436 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12436 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12436 BstLean.Part154.csC) (piBar (rhoBar 12436 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12436 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036190677027 * 1.66825E-7 / (0.000257322699 : ℝ) := by gcongr
    _ ≤ 0.002687093061 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12436 BstLean.Part154.csC Θ ≤ 0.002982566053 + 0.000678982616 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12436 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12436 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12436 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036190677027 : ℝ) * ((2 * Θ * 0.000257323097 +
        (6863 / 10000) * 0.000257323097 * 12436 * 0.001029358604) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002982566053 + 0.000678982616 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12436 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12436 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12436 0.011 Θ ∧ gammaRatio 12436 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12436 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036190677027 : ℝ) * 0.525 / ((1 - 0.011) * 12436) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12436 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12436 0.011 Θ) :=
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
    badAllowance 12436 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12436 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12436 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12436 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12436 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12436 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12436 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12436 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12436 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12436 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12436 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036190677027 : ℝ) * 12436 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12436 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004182566053 + 0.003366075677 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12436

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12436
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12436 BstLean.Part154.csC) (piBar (rhoBar 12436 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12436 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12436 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12436 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12436 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12436 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12436 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12436 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12436 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12436 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12436 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12436 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12436 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12436 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12436 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053044546312 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12436) ≤ 0.010709035964 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12436 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036190677027)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010709035964 + 2 * 0.737676 / 12436) := by gcongr
    _ ≤ (0.053044546312 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12436 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12436

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12436
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491375981 : ℝ) ≤ plow 12436 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12436) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053456355784)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410723858) : eMP 12436 0.011 xi bn ≤ 0.001214224313 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12436 : ℝ) * (1 - 0.011))) ≤ 0.000600284962 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001410723858 / (12436 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000600284962 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000600284962 : ℝ) + 3.141593 * 0.053456355784 / (12436 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001214224313 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053456355784)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410723858) : PiBarMP 12436 12 0.011 xi bn ≤ 0.162974165285 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12436 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037559604072 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.901776360886 : ℝ) ≤ √((12436 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.516814875605 : ℝ) ≤ √(12436 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12436) ≤ 0.124935493166 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037559604072 + 0.053456355784 * 1.772454 / (2 * (110.901776360886 : ℝ))) * (1 + 0.001214224313) +
        8 / (12436 * 111.516814875605) + 0.124935493166 := by gcongr
    _ ≤ (0.162974165285 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053456355784)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410723858) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284250851988) :
    parallelOracle 12436 0.011 xi bn cd ≤ 0.163991089474 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12436 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12436 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491375981 : ℝ) ≤ plow 12436 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.516814875605 : ℝ) ≤ √(12436 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284250851988 : ℝ) / (2 * 0.560491375981 * 111.516814875605)) * 0.162974165285 +
        0.284250851988 ^ 2 / (2 * 0.560491375981 * 111.516814875605) := by gcongr
    _ ≤ (0.163991089474 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053456355784) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410723858)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284250851988) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12436 12436 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491375981 : ℝ) ≤ plow 12436 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.516814875605 : ℝ) ≤ √(12436 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12436 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12436 Θ 1.22 ≤ 0.011891484719 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.516814875605 := by gcongr <;> linarith
      _ ≤ (0.011891484719 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12436 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12436 12436 0.011 ≤ 0.008571685877 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12436 12436 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12436 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12436 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12436 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12436 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163991089474 + 0.011891484719 + (0.008571685877 : ℝ) *
        (1 + 2 * (0.284250851988 + 0.011891484719) / (0.560491375981 * 111.516814875605))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12436]

end BstLean.Part269.N12436

/-! The original eight local profiles supply actual 12436 moment certificates. -/
namespace BstLean.Part269.N12436
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12436 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12436 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12436 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053456355784 ∧
    0 ≤ bN 12436 BstLean.Part154.csC (groupTheta g) ∧ bN 12436 BstLean.Part154.csC (groupTheta g) ≤ 0.001410723858 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12436 12436 0.011
      (momentAllowance 12436 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12436 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12436 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12436 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12436 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12436 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231206305676 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12436 0.011
      (momentAllowance 12436 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12436 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12436
/-! The actual computed-centre upper energy formula at 12436. -/
namespace BstLean.Part269.N12436
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12436

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12436
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12436)
open BstLean.Part268 (cell12436)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086301606343
  | 2 => 0.087260244765
  | 3 => 0.088219495402
  | 4 => 0.089181333806
  | 5 => 0.090148129002
  | 6 => 0.091122699197
  | 7 => 0.092108372232
  | 8 => 0.093109050759
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12436 12436 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12436 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12436

/-! Actual upper energy certificates on all 43 source endpoints at 12436. -/
namespace BstLean.Part269.N12436
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12436)
open BstLean.Part268 (cell12436)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12436 (gMinus 12436) (1 - (cell12436 i).lower) ≤ 1 ∧
    energyUpper 12436 (gMinus 12436) (BstLean.Part211.gPlus 12436)
      (finiteEnergy 12436 12436 0.011) (1 - (cell12436 i).lower) ≤
      (cell12436 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨10,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨11,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨12,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨13,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨14,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨15,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨16,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨17,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨18,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨19,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨20,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨21,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨22,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨23,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨24,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨25,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨26,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨27,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨28,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨29,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨30,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨31,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨32,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨33,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨34,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨35,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨36,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨37,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨38,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨39,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨40,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨41,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨42,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨43,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨44,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨45,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨46,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨47,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨48,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨49,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨50,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨51,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12436) (by norm_num)
        (q := 1 - (cell12436 ⟨52,by decide⟩).lower)
        (by norm_num [cell12436]) (by norm_num [cell12436])
      exact ⟨E.1,E.2.trans (by norm_num [cell12436])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12436

/-! Source-cell containment and simple scalar guards at 12436. -/
namespace BstLean.Part269.N12436
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12436)
open BstLean.Part268 (cell12436)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12436 ⟨10,by decide⟩).lower ∧ (cell12436 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12436 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12436 ⟨11,by decide⟩).lower ∧ (cell12436 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12436 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12436 ⟨12,by decide⟩).lower ∧ (cell12436 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12436 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12436 ⟨13,by decide⟩).lower ∧ (cell12436 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12436 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12436 ⟨14,by decide⟩).lower ∧ (cell12436 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12436 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12436 ⟨15,by decide⟩).lower ∧ (cell12436 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12436 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12436 ⟨16,by decide⟩).lower ∧ (cell12436 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12436 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12436 ⟨17,by decide⟩).lower ∧ (cell12436 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12436 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12436 ⟨18,by decide⟩).lower ∧ (cell12436 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12436 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12436 ⟨19,by decide⟩).lower ∧ (cell12436 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12436 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12436 ⟨20,by decide⟩).lower ∧ (cell12436 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12436 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12436 ⟨21,by decide⟩).lower ∧ (cell12436 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12436 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12436 ⟨22,by decide⟩).lower ∧ (cell12436 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12436 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12436 ⟨23,by decide⟩).lower ∧ (cell12436 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12436 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12436 ⟨24,by decide⟩).lower ∧ (cell12436 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12436 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12436 ⟨25,by decide⟩).lower ∧ (cell12436 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12436 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12436 ⟨26,by decide⟩).lower ∧ (cell12436 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12436 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12436 ⟨27,by decide⟩).lower ∧ (cell12436 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12436 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12436 ⟨28,by decide⟩).lower ∧ (cell12436 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12436 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12436 ⟨29,by decide⟩).lower ∧ (cell12436 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12436 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12436 ⟨30,by decide⟩).lower ∧ (cell12436 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12436 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12436 ⟨31,by decide⟩).lower ∧ (cell12436 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12436 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12436 ⟨32,by decide⟩).lower ∧ (cell12436 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12436 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12436 ⟨33,by decide⟩).lower ∧ (cell12436 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12436 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12436 ⟨34,by decide⟩).lower ∧ (cell12436 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12436 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12436 ⟨35,by decide⟩).lower ∧ (cell12436 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12436 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12436 ⟨36,by decide⟩).lower ∧ (cell12436 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12436 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12436 ⟨37,by decide⟩).lower ∧ (cell12436 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12436 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12436 ⟨38,by decide⟩).lower ∧ (cell12436 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12436 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12436 ⟨39,by decide⟩).lower ∧ (cell12436 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12436 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12436 ⟨40,by decide⟩).lower ∧ (cell12436 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12436 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12436 ⟨41,by decide⟩).lower ∧ (cell12436 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12436 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12436 ⟨42,by decide⟩).lower ∧ (cell12436 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12436 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12436 ⟨43,by decide⟩).lower ∧ (cell12436 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12436 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12436 ⟨44,by decide⟩).lower ∧ (cell12436 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12436 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12436 ⟨45,by decide⟩).lower ∧ (cell12436 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12436 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12436 ⟨46,by decide⟩).lower ∧ (cell12436 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12436 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12436 ⟨47,by decide⟩).lower ∧ (cell12436 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12436 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12436 ⟨48,by decide⟩).lower ∧ (cell12436 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12436 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12436 ⟨49,by decide⟩).lower ∧ (cell12436 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12436 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12436 ⟨50,by decide⟩).lower ∧ (cell12436 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12436 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12436 ⟨51,by decide⟩).lower ∧ (cell12436 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12436 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12436 ⟨52,by decide⟩).lower ∧ (cell12436 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12436 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12436 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12436 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12436,cell12436,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12436 i).lower ∧
    (cell12436 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12436 i).upper ≤ (0.532 : ℝ) ∧
    (cell12436 i).centre ≤ (0.1 : ℝ) ∧ (cell12436 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12436 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12436 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12436

/-! The local source numeric instances at 12436 have no network premises. -/
namespace BstLean.Part269.N12436
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12436)
open BstLean.Part268 (cell12436)

noncomputable def sourceNumerics12436 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12436 (cell12436 i)
      scalarRow12436.M scalarRow12436.H scalarRow12436.xi := by
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
    energy_allowance := scalarRow12436.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12436]
    centre_nonneg := (scalarRow12436.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12436])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12436
/-! Actual 12437 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12437
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12437 ≤ (1.036189209107 : ℝ) := by
  have hr : (111.521298414249 : ℝ) ≤ √(12437 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.521298414249 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12437 12437 (11 / 1000) ≤
    (0.008571341263 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12437) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.521298414249 : ℝ) ≤ √(12437 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12437)
  have hdiv : K / √(12437 : ℝ) ≤ K / 111.521298414249 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.521298414249 ≤ (0.008571341263 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12437.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12437 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12437 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12437 := gPlus_lower 12437
end BstLean.Part269.N12437

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12437
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036189209106 : ℝ) ≤ wn 12437 := by
  have hn : √(12437 : ℝ) ≤ 111.521298414250 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12437 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.521298414250 ≤ 2 / √(12437 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257301644 : ℝ) ≤ rhoBar 12437 BstLean.Part154.csC ∧
    rhoBar 12437 BstLean.Part154.csC ≤ 0.000257302043 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036189209106 : ℝ) / (1.295212 * 12437) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036189209107 : ℝ) / (1.29521 * 12437) := by gcongr
      _ ≤ (0.000257302043 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12437 BstLean.Part154.csC) ≤ 0.001029274377 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12437 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12437 BstLean.Part154.csC) (piBar (rhoBar 12437 BstLean.Part154.csC)) ≤ 0.000196529233 ∧
    cc1 (rhoBar 12437 BstLean.Part154.csC) (piBar (rhoBar 12437 BstLean.Part154.csC)) ≤ 0.000125052815 ∧
    cc2 (rhoBar 12437 BstLean.Part154.csC) ≤ 0.000072594068 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12437 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12437 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12437 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12437 BstLean.Part154.csC * nuR (rhoBar 12437 BstLean.Part154.csC)) ≤ 0.000514620637 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257302043 : ℝ) * 0.001029274377 := by gcongr
      _ ≤ (0.000514620637 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12437 BstLean.Part154.csC) * nuR (rhoBar 12437 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001029274377 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12437 BstLean.Part154.csC) * rhoBar 12437 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257302043 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257302043 / 2 + 0.399 * 0.001029274377 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196529233 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514620637 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125052815 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257302043 / 1.414213562 := by gcongr
      _ ≤ (0.000072594068 : ℝ) := by norm_num

end BstLean.Part269.N12437

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12437
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12437 BstLean.Part154.csC) (piBar (rhoBar 12437 BstLean.Part154.csC)) ≤ 1.66797E-7 := by
  have hr0 : 0 ≤ rhoBar 12437 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12437 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12437 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12437 BstLean.Part154.csC) (piBar (rhoBar 12437 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12437 BstLean.Part154.csC) (piBar (rhoBar 12437 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12437 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196529233 : ℝ) ^ 2 + 0.000125052815 ^ 2 + 3 * 0.000072594068 ^ 2 +
        2 * 0.797885 * 0.000196529233 * 0.000125052815 + 2 * 0.000196529233 * 0.000072594068 +
        4 * 0.797885 * 0.000125052815 * 0.000072594068 := by gcongr
    _ ≤ (1.66797E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12437 BstLean.Part154.csC Θ ≤ 0.002686858099 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12437 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12437 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12437 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12437 BstLean.Part154.csC) (piBar (rhoBar 12437 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12437 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036189209107 * 1.66797E-7 / (0.000257301644 : ℝ) := by gcongr
    _ ≤ 0.002686858099 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12437 BstLean.Part154.csC Θ ≤ 0.002982313563 + 0.000678926100 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12437 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12437 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12437 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036189209107 : ℝ) * ((2 * Θ * 0.000257302043 +
        (6863 / 10000) * 0.000257302043 * 12437 * 0.001029274377) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002982313563 + 0.000678926100 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12437 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12437 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12437 0.011 Θ ∧ gammaRatio 12437 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12437 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036189209107 : ℝ) * 0.525 / ((1 - 0.011) * 12437) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12437 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12437 0.011 Θ) :=
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
    badAllowance 12437 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0012 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12437 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12437 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12437 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12437 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12437 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12437 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12437 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12437 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12437 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12437 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036189209107 : ℝ) * 12437 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0012 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12437 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004182313563 + 0.003365784199 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12437

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12437
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12437 BstLean.Part154.csC) (piBar (rhoBar 12437 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12437 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12437 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12437 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12437 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12437 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12437 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12437 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12437 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12437 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12437 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12437 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12437 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12437 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12437 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053042390375 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12437) ≤ 0.010708605424 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12437 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036189209107)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010708605424 + 2 * 0.737676 / 12437) := by gcongr
    _ ≤ (0.053042390375 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12437 12 ≤ 0.0015 := by
  exact BstLean.Part269.S3.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12437

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12437
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560491423140 : ℝ) ≤ plow 12437 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12437) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053455950268)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410600502) : eMP 12437 0.011 xi bn ≤ 0.001214122356 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12437 : ℝ) * (1 - 0.011))) ≤ 0.000600234584 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001410600502 / (12437 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000600234584 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000600234584 : ℝ) + 3.141593 * 0.053455950268 / (12437 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001214122356 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053455950268)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410600502) : PiBarMP 12437 12 0.011 xi bn ≤ 0.162967473275 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12437 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037557961899 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.906235171878 : ℝ) ≤ √((12437 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.521298414249 : ℝ) ≤ √(12437 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12437) ≤ 0.124930470331 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037557961899 + 0.053455950268 * 1.772454 / (2 * (110.906235171878 : ℝ))) * (1 + 0.001214122356) +
        8 / (12437 * 111.521298414249) + 0.124930470331 := by gcongr
    _ ≤ (0.162967473275 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053455950268)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410600502) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284247819092) :
    parallelOracle 12437 0.011 xi bn cd ≤ 0.163984323533 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12437 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12437 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560491423140 : ℝ) ≤ plow 12437 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.521298414249 : ℝ) ≤ √(12437 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284247819092 : ℝ) / (2 * 0.560491423140 * 111.521298414249)) * 0.162967473275 +
        0.284247819092 ^ 2 / (2 * 0.560491423140 * 111.521298414249) := by gcongr
    _ ≤ (0.163984323533 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053455950268) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001410600502)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284247819092) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12437 12437 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560491423140 : ℝ) ≤ plow 12437 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.521298414249 : ℝ) ≤ √(12437 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12437 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12437 Θ 1.22 ≤ 0.011891006641 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.521298414249 := by gcongr <;> linarith
      _ ≤ (0.011891006641 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12437 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12437 12437 0.011 ≤ 0.008571341263 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12437 12437 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12437 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12437 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12437 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12437 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163984323533 + 0.011891006641 + (0.008571341263 : ℝ) *
        (1 + 2 * (0.284247819092 + 0.011891006641) / (0.560491423140 * 111.521298414249))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12437]

end BstLean.Part269.N12437

/-! The original eight local profiles supply actual 12437 moment certificates. -/
namespace BstLean.Part269.N12437
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12437 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12437 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12437 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053455950268 ∧
    0 ≤ bN 12437 BstLean.Part154.csC (groupTheta g) ∧ bN 12437 BstLean.Part154.csC (groupTheta g) ≤ 0.001410600502 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12437 12437 0.011
      (momentAllowance 12437 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12437 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12437 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12437 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12437 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12437 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231205428717 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12437 0.011
      (momentAllowance 12437 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12437 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12437
/-! The actual computed-centre upper energy formula at 12437. -/
namespace BstLean.Part269.N12437
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12437

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12437
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12437)
open BstLean.Part268 (cell12437)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086298361585
  | 2 => 0.087256932441
  | 3 => 0.088216104418
  | 4 => 0.089177850616
  | 5 => 0.090144537191
  | 6 => 0.091118979014
  | 7 => 0.092104500080
  | 8 => 0.093104998623
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12437 12437 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12437 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12437

/-! Actual upper energy certificates on all 43 source endpoints at 12437. -/
namespace BstLean.Part269.N12437
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12437)
open BstLean.Part268 (cell12437)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12437 (gMinus 12437) (1 - (cell12437 i).lower) ≤ 1 ∧
    energyUpper 12437 (gMinus 12437) (BstLean.Part211.gPlus 12437)
      (finiteEnergy 12437 12437 0.011) (1 - (cell12437 i).lower) ≤
      (cell12437 i).energy := by
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
      have E := BstLean.Part269.S3.uniformEnergy10 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨10,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy11 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨11,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy12 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨12,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy13 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨13,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy14 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨14,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy15 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨15,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy16 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨16,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy17 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨17,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy18 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨18,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy19 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨19,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy20 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨20,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy21 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨21,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy22 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨22,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy23 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨23,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy24 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨24,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy25 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨25,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy26 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨26,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy27 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨27,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy28 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨28,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy29 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨29,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy30 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨30,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy31 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨31,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy32 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨32,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy33 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨33,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy34 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨34,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy35 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨35,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy36 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨36,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy37 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨37,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy38 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨38,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy39 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨39,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy40 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨40,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy41 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨41,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy42 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨42,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy43 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨43,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy44 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨44,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy45 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨45,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy46 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨46,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy47 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨47,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy48 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨48,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy49 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨49,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy50 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨50,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy51 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨51,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S3.uniformEnergy52 (n := 12437) (by norm_num)
        (q := 1 - (cell12437 ⟨52,by decide⟩).lower)
        (by norm_num [cell12437]) (by norm_num [cell12437])
      exact ⟨E.1,E.2.trans (by norm_num [cell12437])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12437

/-! Source-cell containment and simple scalar guards at 12437. -/
namespace BstLean.Part269.N12437
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12437)
open BstLean.Part268 (cell12437)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12437 ⟨10,by decide⟩).lower ∧ (cell12437 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12437 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12437 ⟨11,by decide⟩).lower ∧ (cell12437 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12437 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12437 ⟨12,by decide⟩).lower ∧ (cell12437 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12437 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12437 ⟨13,by decide⟩).lower ∧ (cell12437 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12437 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12437 ⟨14,by decide⟩).lower ∧ (cell12437 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12437 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12437 ⟨15,by decide⟩).lower ∧ (cell12437 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12437 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12437 ⟨16,by decide⟩).lower ∧ (cell12437 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12437 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12437 ⟨17,by decide⟩).lower ∧ (cell12437 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12437 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12437 ⟨18,by decide⟩).lower ∧ (cell12437 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12437 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12437 ⟨19,by decide⟩).lower ∧ (cell12437 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12437 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12437 ⟨20,by decide⟩).lower ∧ (cell12437 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12437 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12437 ⟨21,by decide⟩).lower ∧ (cell12437 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12437 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12437 ⟨22,by decide⟩).lower ∧ (cell12437 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12437 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12437 ⟨23,by decide⟩).lower ∧ (cell12437 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12437 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12437 ⟨24,by decide⟩).lower ∧ (cell12437 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12437 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12437 ⟨25,by decide⟩).lower ∧ (cell12437 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12437 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12437 ⟨26,by decide⟩).lower ∧ (cell12437 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12437 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12437 ⟨27,by decide⟩).lower ∧ (cell12437 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12437 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12437 ⟨28,by decide⟩).lower ∧ (cell12437 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12437 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12437 ⟨29,by decide⟩).lower ∧ (cell12437 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12437 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12437 ⟨30,by decide⟩).lower ∧ (cell12437 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12437 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12437 ⟨31,by decide⟩).lower ∧ (cell12437 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12437 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12437 ⟨32,by decide⟩).lower ∧ (cell12437 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12437 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12437 ⟨33,by decide⟩).lower ∧ (cell12437 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12437 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12437 ⟨34,by decide⟩).lower ∧ (cell12437 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12437 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12437 ⟨35,by decide⟩).lower ∧ (cell12437 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12437 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12437 ⟨36,by decide⟩).lower ∧ (cell12437 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12437 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12437 ⟨37,by decide⟩).lower ∧ (cell12437 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12437 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12437 ⟨38,by decide⟩).lower ∧ (cell12437 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12437 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12437 ⟨39,by decide⟩).lower ∧ (cell12437 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12437 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12437 ⟨40,by decide⟩).lower ∧ (cell12437 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12437 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12437 ⟨41,by decide⟩).lower ∧ (cell12437 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12437 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12437 ⟨42,by decide⟩).lower ∧ (cell12437 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12437 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12437 ⟨43,by decide⟩).lower ∧ (cell12437 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12437 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12437 ⟨44,by decide⟩).lower ∧ (cell12437 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12437 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12437 ⟨45,by decide⟩).lower ∧ (cell12437 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12437 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12437 ⟨46,by decide⟩).lower ∧ (cell12437 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12437 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12437 ⟨47,by decide⟩).lower ∧ (cell12437 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12437 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12437 ⟨48,by decide⟩).lower ∧ (cell12437 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12437 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12437 ⟨49,by decide⟩).lower ∧ (cell12437 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12437 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12437 ⟨50,by decide⟩).lower ∧ (cell12437 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12437 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12437 ⟨51,by decide⟩).lower ∧ (cell12437 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12437 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12437 ⟨52,by decide⟩).lower ∧ (cell12437 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12437 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12437 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12437 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12437,cell12437,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12437 i).lower ∧
    (cell12437 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12437 i).upper ≤ (0.532 : ℝ) ∧
    (cell12437 i).centre ≤ (0.1 : ℝ) ∧ (cell12437 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12437 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12437 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12437

/-! The local source numeric instances at 12437 have no network premises. -/
namespace BstLean.Part269.N12437
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12437)
open BstLean.Part268 (cell12437)

noncomputable def sourceNumerics12437 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12437 (cell12437 i)
      scalarRow12437.M scalarRow12437.H scalarRow12437.xi := by
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
    energy_allowance := scalarRow12437.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12437]
    centre_nonneg := (scalarRow12437.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D3.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12437])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12437